// Copyright (c) 2026 Mizar. Apache-2.0; see LICENSE.
#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <memory>
#include <map>
#include <mutex>
#include <numeric>
#include <shared_mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <type_traits>
#include <vector>

using u64 = uint64_t;
using i128 = __int128;
using u128 = unsigned __int128;
namespace fs = std::filesystem;

// Negative witnesses accept 0 and +1 below threshold; non-one accepts only +1.
// Reuses FastMod, normalized CRT coordinates, recursive wheels and 8-lane
// filtering from the audited non-one search. Output is chunk minima, not
// the potentially billions of matching inputs. Full reduction emits records.
static bool NON_ONE=false;
static int THRESHOLD=131;
static unsigned BITS=64;
// Zero is the exclusive-bound sentinel for 2^128, never an input value.
static u128 LIMIT=0, OUTPUT_HI=0;
static bool HAS_LIMIT=false, FULL_LIMIT=false;
static constexpr u128 U128_MAX = ~u128(0);
static const std::string TWO128 = "340282366920938463463374607431768211456";
static int ROOT_PRIME=0, ROOT_EXP=0, FILTER_LIMIT=130;
static int WHEEL_LIMIT=0;
static u64 MULTIPLIER=1;
static int COEFFICIENT_SYMBOL[1000];
static u128 N_MIN = 1, OUTPUT_LO = 1;
static u128 N_HI = (u128)1 << 64;
static u128 N_MAX = N_HI - 1;
static constexpr u64 UMAX = ~u64(0);
static constexpr u64 DIRECT_RANGE_MAX_SPAN = 1ULL << 20;
static std::atomic<bool> g_stop{false};
static void on_signal(int) { g_stop = 1; }

static u64 mul_mod(u64 a, u64 b, u64 m) { return (u128)a * b % m; }
static u64 pow_mod(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  while (e) {
    if (e & 1)
      r = mul_mod(r, a, m);
    a = mul_mod(a, a, m);
    e >>= 1;
  }
  return r;
}
static int legendre(u64 a, int p) {
  a %= u64(p);
  if (!a)
    return 0;
  return pow_mod(a, (p - 1) / 2, p) == 1 ? 1 : -1;
}
// Constraints on the quotient m, where the original input n=C*m.
static bool allow_m(int q,int value) {
  if(!ROOT_PRIME) return q>=THRESHOLD || (NON_ONE ? value==1 : value!=-1);
  if(q==ROOT_PRIME) return ROOT_EXP==1 ? value!=0 : value==-1;
  int original=value*COEFFICIENT_SYMBOL[q];
  if(q<ROOT_PRIME) return original==1;
  if(q<THRESHOLD) return original!=-1;
  return true;
}
static int legendre128(u128 a, int p) {
  u64 r = (u64)(a % (u64)p);
  if (!r)
    return 0;
  return pow_mod(r, (p - 1) / 2, p) == 1 ? 1 : -1;
}
static u64 inv_mod(u64 a, u64 m) {
  i128 t = 0, nt = 1;
  u64 r = m, nr = a % m;
  while (nr) {
    u64 q = r / nr;
    u64 rr = r - q * nr;
    r = nr;
    nr = rr;
    auto tt = t - (i128)q * nt;
    t = nt;
    nt = tt;
  }
  assert(r == 1);
  t %= m;
  if (t < 0)
    t += m;
  return (u64)t;
}
static std::vector<int> odd_primes_upto(int n) {
  std::vector<int> v;
  for (int x = 3; x <= n; x += 2) {
    bool ok = 1;
    for (int d = 3; 1LL * d * d <= x; d += 2)
      if (x % d == 0) {
        ok = 0;
        break;
      }
    if (ok)
      v.push_back(x);
  }
  return v;
}
static bool is_prime_small(int x) {
  if (x < 2)
    return false;
  if ((x & 1) == 0)
    return x == 2;
  for (int d = 3; 1LL * d * d <= x; d += 2)
    if (x % d == 0)
      return false;
  return true;
}
static int next_odd_prime(int p) {
  for (int q = p + 2;; q += 2)
    if (is_prime_small(q))
      return q;
}

static inline bool is_square_u128(u128 x) {
  // The floating estimate can round to 2^64, outside the u64 range.
  long double estimate = std::sqrt((long double)x);
  u64 r = estimate >= std::ldexp(1.0L, 64) ? UMAX : (u64)estimate;
  while ((u128)r * r > x)
    --r;
  while (r != UMAX && (u128)(r + 1) * (r + 1) <= x)
    ++r;
  return (u128)r * r == x;
}
static std::string to_string_u128(u128 x) {
  if (x == 0)
    return "0";
  char b[64];
  int n = 0;
  while (x) {
    b[n++] = char('0' + x % 10);
    x /= 10;
  }
  std::string s(n, '0');
  for (int i = 0; i < n; i++)
    s[i] = b[n - 1 - i];
  return s;
}
static std::string upper_exclusive_text() {
  return OUTPUT_HI == 0 ? TWO128 : to_string_u128(OUTPUT_HI);
}
static u128 parse_u128(const std::string &s) {
  if (s.empty()) throw std::runtime_error("empty integer");
  u128 result = 0;
  for (char c : s) {
    if (c < '0' || c > '9') throw std::runtime_error("invalid unsigned integer");
    unsigned digit = c - '0';
    if (result > (U128_MAX - digit) / 10)
      throw std::runtime_error("integer exceeds 2^128-1");
    result = result * 10 + digit;
  }
  return result;
}
static inline int bit_length_u128(u128 x) {
  u64 hi = (u64)(x >> 64);
  if (hi)
    return 64 + (64 - __builtin_clzll(hi));
  u64 lo = (u64)x;
  return lo ? 64 - __builtin_clzll(lo) : 0;
}

struct FastMod {
  u64 m = 1, mu = 0, r64 = 0;
  FastMod() {}
  explicit FastMod(u64 q)
      : m(q), mu((u64)(((u128)1 << 64) / q)), r64((u64)(((u128)1 << 64) % q)) {}
  inline u64 mod(u64 x) const {
    if (m == 1) return 0;
    u64 q = (u64)(((u128)x * mu) >> 64);
    u64 r = x - q * m;
    if (r >= m)
      r -= m;
    return r;
  }
  inline u64 mod128(u128 x) const {
    u64 hi = (u64)(x >> 64), lo = (u64)x;
    u64 a = mod(lo);
    // Reduce hi before multiplying: hi can use all 64 bits, while m<2^32.
    u64 b = mod(mod(hi) * r64);
    u64 s = a + b;
    if (s >= m)
      s -= m;
    return s;
  }
};

struct PassGroup {
  u64 m = 1;
  FastMod fm;
  std::vector<int> ps;
  std::vector<u64> bits;
  PassGroup() {}
  explicit PassGroup(std::vector<int> g) : ps(std::move(g)) {
    for (int p : ps)
      m *= u64(p);
    if (m >= (1ULL << 32)) {
      std::cerr << "group modulus too large\n";
      std::abort();
    }
    fm = FastMod(m);
    bits.assign((size_t)((m + 63) >> 6), 0);
    std::vector<std::vector<uint8_t>> qr;
    for (int p : ps) {
      qr.emplace_back(p, 0);
      for (int x = 1; x < p; x++)
        qr.back()[1LL * x * x % p] = 1;
      qr.back()[0] = 1;
    }
    for (u64 r = 0; r < m; r++) {
      bool ok = true;
      for (size_t j = 0; j < ps.size(); j++)
        if (!allow_m(ps[j],r%ps[j]==0?0:(qr[j][r%ps[j]]?1:-1))) {
          ok = false;
          break;
        }
      if (ok)
        bits[(size_t)(r >> 6)] |= 1ULL << (r & 63);
    }
  }
  inline bool operator()(u128 x) const {
    u64 r = fm.mod128(x);
    return (bits[(size_t)(r >> 6)] >> (r & 63)) & 1ULL;
  }
};

struct CoordGroup {
  u64 m = 1;
  FastMod fm;
  std::vector<int> ps;
  std::vector<u64> bits;
  u64 amul = 0, bmul = 0;
  CoordGroup() {}
  CoordGroup(std::vector<int> g, u64 Mp, u64 Mn) : ps(std::move(g)) {
    for (int p : ps)
      m *= u64(p);
    if (m >= (1ULL << 32)) {
      std::cerr << "coord group modulus too large\n";
      std::abort();
    }
    fm = FastMod(m);
    // Normalize x = Mn*tp - Mp*tn by Mp:
    //   x = Mp * (tp * Mn * Mp^{-1} - tn).
    // Therefore B keys are just tn mod m (one reciprocal reduction), while
    // the table for each p accepts character (Mp/p), not necessarily +1.
    u64 mp = fm.mod(Mp);
    u64 invmp = inv_mod(mp, m);
    amul = fm.mod(fm.mod(Mn) * invmp);
    bmul = 1;
    bits.assign((size_t)((m + 63) >> 6), 0);
    std::vector<std::vector<uint8_t>> qr;
    std::vector<int> want;
    for (int p : ps) {
      qr.emplace_back(p, 0);
      for (int x = 1; x < p; x++)
        qr.back()[1LL * x * x % p] = 1;
      qr.back()[0] = 1;
      want.push_back(legendre(Mp % u64(p), p));
      assert(want.back() != 0);
    }
    for (u64 r = 0; r < m; r++) {
      bool ok = true;
      for (size_t j = 0; j < ps.size(); j++) {
        u64 rp = r % u64(ps[j]);
        if (!allow_m(ps[j],want[j]*(rp==0?0:(qr[j][rp]?1:-1)))) {
          ok = false;
          break;
        }
      }
      if (ok)
        bits[(size_t)(r >> 6)] |= 1ULL << (r & 63);
    }
  }
  template <typename Coord> inline uint32_t akey(Coord tp) const {
    u64 r;
    if constexpr (std::is_same_v<Coord, u64>) r = fm.mod(tp);
    else r = fm.mod128(tp);
    return (uint32_t)fm.mod(r * amul);
  }
  inline uint32_t bkey(u64 tn) const { return (uint32_t)fm.mod(tn); }
  inline bool pass(uint32_t a, uint32_t b) const {
    u64 r = (a >= b) ? u64(a - b) : u64(a) + m - b;
    return (bits[(size_t)(r >> 6)] >> (r & 63)) & 1ULL;
  }
};

struct FirstFailGroup {
  u64 m = 1;
  FastMod fm;
  std::vector<int> ps;
  std::vector<uint8_t> code;
  FirstFailGroup() {}
  explicit FirstFailGroup(std::vector<int> g) : ps(std::move(g)) {
    for (int p : ps)
      m *= u64(p);
    if (m >= (1ULL << 32)) {
      std::cerr << "tail group modulus too large\n";
      std::abort();
    }
    fm = FastMod(m);
    code.resize((size_t)m);
    std::vector<std::vector<uint8_t>> qr;
    for (int p : ps) {
      qr.emplace_back(p, 0);
      for (int x = 1; x < p; x++)
        qr.back()[1LL * x * x % p] = 1;
      qr.back()[0] = 1;
    }
    for (u64 r = 0; r < m; r++) {
      uint8_t c = 0;
      for (size_t j = 0; j < ps.size(); j++) {
        u64 a = r % u64(ps[j]);
        if ((NON_ONE && a == 0) || (a != 0 && !qr[j][a])) {
          c = (uint8_t)(2 * j + (a == 0 ? 2 : 1));
          break;
        }
      }
      code[(size_t)r] = c;
    }
  }
  inline uint8_t classify(u128 x) const { return code[(size_t)fm.mod128(x)]; }
  inline int prime_of(uint8_t c) const { return ps[(c - 1) >> 1]; }
  inline int chi_of(uint8_t c) const { return (c & 1) ? -1 : 0; }
};

// Sorenson-style normalized sieve for a small prime q.
// For fixed tn, n = Mn*(tp - shift) mod q, where
// shift = tn*Mp*Mn^{-1} mod q.  We table [shift][tp mod q].
struct NormPrime {
  int q = 0;
  u64 k = 0;
  int want = 1;
  FastMod fm;
  std::vector<uint8_t> table, shift_lut;
  NormPrime() {}
  NormPrime(int qq, u64 Mp, u64 Mn) : q(qq), fm((u64)qq) {
    u64 invMn = inv_mod(fm.mod(Mn), u64(q));
    k = (fm.mod(Mp) * invMn) % u64(q);
    want = legendre(fm.mod(Mn), q);
    shift_lut.resize(q);
    for (int r = 0; r < q; r++)
      shift_lut[r] = (uint8_t)((u64)r * k % u64(q));
    table.resize((size_t)q * q);
    for (int sh = 0; sh < q; sh++)
      for (int r = 0; r < q; r++) {
        int d = r - sh;
        if (d < 0)
          d += q;
        table[(size_t)sh * q + r] = (uint8_t)(legendre((u64)d, q) == want);
      }
  }
  inline uint8_t residue(u64 tp) const { return (uint8_t)fm.mod(tp); }
  inline int shift(u64 tn) const { return shift_lut[(size_t)fm.mod(tn)]; }
  inline bool pass(int sh, uint8_t r) const {
    return table[(size_t)sh * q + r] != 0;
  }
};

struct WheelLevel {
  int p = 0, allowed_count = 0;
  u64 step = 0;
  FastMod fm;
  std::vector<uint8_t> allowed;
  std::vector<u64> jump;
  std::vector<uint16_t> next, child_delta;
};
struct Wheel {
  u64 base_mod = 1, base_res = 0, residue_count = 1, period = 1;
  std::vector<WheelLevel> L;
  // Combined tail for the last two super-levels.  dist[y] is the distance
  // from y to the next allowed y, including y itself (hence 0 iff allowed).
  u64 tail_q = 1, tail_step = 1, tail_inv_step = 1;
  FastMod tail_fm;
  std::vector<uint8_t> tail_dist;
  std::vector<uint32_t> tail_delta3;
  Wheel() {}
  Wheel(u64 bm, u64 br, const std::vector<int> &ps,
        const std::vector<int> &want, const std::vector<int> &group_sizes)
      : base_mod(bm), base_res(br) {
    assert(ps.size() == want.size());
    size_t at = 0;
    u64 m = bm;
    for (int gs : group_sizes) {
      assert(gs > 0 && at + (size_t)gs <= ps.size());
      int q = 1;
      for (int z = 0; z < gs; z++) {
        if ((u64)q * ps[at + z] >= 65536) {
          std::cerr << "wheel super-level modulus too large\n";
          std::abort();
        }
        q *= ps[at + z];
      }
      WheelLevel w;
      w.p = q;
      w.step = m;
      w.fm = FastMod(q);
      w.allowed.assign(q, 0);
      w.jump.assign(q, 0);
      w.next.assign(q, 0);
      for (int r = 0; r < q; r++) {
        bool ok = true;
        for (int z = 0; z < gs; z++)
          if (!allow_m(ps[at+z],want[at+z]*legendre((u64)(r%ps[at+z]),ps[at+z]))) {
            ok = false;
            break;
          }
        if (ok) {
          w.allowed[r] = 1;
          ++w.allowed_count;
        }
      }
      u64 sm = m % u64(q);
      std::vector<uint8_t> ay(q);
      for (int y = 0; y < q; y++)
        ay[y] = w.allowed[(u64)y * sm % u64(q)];
      std::vector<int> apos;
      for (int y = 0; y < q; y++)
        if (ay[y])
          apos.push_back(y);
      assert(!apos.empty());
      for (int y = 0; y < q; y++) {
        auto it = std::upper_bound(apos.begin(), apos.end(), y);
        int ny = (it == apos.end() ? apos.front() + q : *it);
        int d = ny - y;
        u64 r = (u64)y * sm % u64(q);
        u64 nr = (u64)(ny % q) * sm % u64(q);
        u128 jp = (u128)d * m;
        if (jp > UMAX) {
          std::cerr << "wheel jump overflow\n";
          std::abort();
        }
        w.jump[r] = (u64)jp;
        w.next[r] = (uint16_t)nr;
      }
      L.push_back(std::move(w));
      residue_count *= u64(L.back().allowed_count);
      u128 nm = (u128)m * q;
      if (nm > UMAX) {
        std::cerr << "wheel modulus overflow\n";
        std::abort();
      }
      m = (u64)nm;
      at += gs;
    }
    assert(at == ps.size());
    period=m;
    for (size_t i = 0; i + 1 < L.size(); i++) {
      auto &z = L[i];
      u64 cp = L[i + 1].p;
      z.child_delta.resize(z.p);
      for (int r = 0; r < z.p; r++)
        z.child_delta[r] = (uint16_t)(z.jump[r] % cp);
    }
    if (L.size() != 6) return;
    // Collapse levels 4 and 5 into one cache-friendly uint8_t distance table.
    tail_step = L[4].step;
    tail_q = u64(L[4].p) * u64(L[5].p);
    if (tail_q > UINT32_MAX) {
      std::cerr << "tail modulus too large\n";
      std::abort();
    }
    tail_fm = FastMod(tail_q);
    tail_inv_step = inv_mod(tail_step % tail_q, tail_q);
    std::vector<uint8_t> ok((size_t)tail_q, 0);
    tail_dist.resize((size_t)tail_q);
    const u64 s4 = tail_step % u64(L[4].p), s5 = tail_step % u64(L[5].p);
    u64 cnt = 0;
    for (u64 y = 0; y < tail_q; y++) {
      if (L[4].allowed[(u64)((u128)(y % u64(L[4].p)) * s4 % u64(L[4].p))] &&
          L[5].allowed[(u64)((u128)(y % u64(L[5].p)) * s5 % u64(L[5].p))]) {
        ok[(size_t)y] = 1;
        ++cnt;
      }
    }
    assert(cnt == u64(L[4].allowed_count) * u64(L[5].allowed_count));
    long long nxt = -1;
    unsigned maxd = 0;
    for (long long yy = (long long)(2 * tail_q) - 1; yy >= 0; --yy) {
      u64 y = u64(yy) % tail_q;
      if (ok[(size_t)y])
        nxt = yy;
      if ((u64)yy < tail_q) {
        assert(nxt >= 0);
        u64 d = u64(nxt - yy);
        assert(d <= 255);
        tail_dist[(size_t)y] = (uint8_t)d;
        maxd = std::max<unsigned>(maxd, (unsigned)d);
      }
    }
    if ((u128)(maxd + 1) * tail_step > UMAX) {
      std::cerr << "tail jump overflow\n";
      std::abort();
    }
    // At level 3, advancing by L3.jump changes y=x/tail_step mod tail_q by this
    // amount.
    auto const &z = L[3];
    tail_delta3.resize((size_t)z.p);
    for (int r = 0; r < z.p; r++) {
      u64 jr = tail_fm.mod(z.jump[(size_t)r]);
      tail_delta3[(size_t)r] = (uint32_t)tail_fm.mod(jr * tail_inv_step);
    }
  }
  template <typename Coord> inline __attribute__((always_inline)) void
  emit_tail(Coord x, Coord hi, std::vector<Coord> &out, uint32_t y) const {
    const Coord span = hi - x;
    uint32_t d = tail_dist[(size_t)y];
    if (d) {
      u64 j = u64(d) * tail_step;
      if (j >= span)
        return;
      x += j;
      y += d;
      if (y >= tail_q)
        y -= tail_q;
    }
    if (x >= hi)
      return;
    out.push_back(x);
    // Default qr80 chunks are much shorter than tail_step, so a tail class
    // can contribute at most one coordinate.  Avoid computing the next hit.
    if (tail_step >= span)
      return;
    for (;;) {
      uint32_t y1 = y + 1;
      if (y1 == tail_q)
        y1 = 0;
      uint32_t gap = 1u + tail_dist[(size_t)y1];
      u64 j = u64(gap) * tail_step;
      if (j >= hi - x)
        break;
      x += j;
      y += gap;
      if (y >= tail_q)
        y -= tail_q;
      out.push_back(x);
    }
  }
  template <size_t I, typename Coord>
  inline __attribute__((always_inline)) void
  rec6(Coord x, Coord hi, std::vector<Coord> &out, u64 r) const {
    if (x >= hi)
      return;
    auto const &z = L[I];
    if (!z.allowed[r]) {
      u64 j = z.jump[r];
      if (j >= hi - x)
        return;
      x += j;
      r = z.next[r];
    }
    if constexpr (I == 3) {
      uint32_t ty = (uint32_t)tail_fm.mod(tail_fm.mod128(x) * tail_inv_step);
      for (int c = 0; c < z.allowed_count && x < hi; c++) {
        emit_tail(x, hi, out, ty);
        u64 oldr = r, j = z.jump[oldr];
        if (j >= hi - x)
          break;
        x += j;
        r = z.next[oldr];
        ty += (uint32_t)tail_delta3[(size_t)oldr];
        if (ty >= tail_q)
          ty -= tail_q;
      }
    } else if constexpr (I < 3) {
      auto const &ch = L[I + 1];
      u64 cr = ch.fm.mod128(x);
      for (int c = 0; c < z.allowed_count && x < hi; c++) {
        rec6<I + 1>(x, hi, out, cr);
        u64 oldr = r, j = z.jump[oldr];
        if (j >= hi - x)
          break;
        x += j;
        r = z.next[oldr];
        cr += z.child_delta[oldr];
        if (cr >= u64(ch.p))
          cr -= u64(ch.p);
      }
    }
  }
  template <typename Coord>
  void generic(size_t i, Coord x, Coord hi, std::vector<Coord>& out) const {
    if (x >= hi) return;
    if (i == L.size()) { out.push_back(x); return; }
    auto const& z=L[i];
    u64 r=z.fm.mod128(x);
    if (!z.allowed[r]) {
      u64 j=z.jump[r]; if (j >= hi-x) return;
      x+=j; r=z.next[r];
    }
    for (int c=0;c<z.allowed_count && x<hi;++c) {
      generic(i+1,x,hi,out);
      u64 j=z.jump[r]; if (j >= hi-x) break;
      x+=j; r=z.next[r];
    }
  }
  template <typename Coord>
  void generate_segment(Coord lo, Coord hi, std::vector<Coord> &out) const {
    if (lo >= hi)
      return;
    u64 rem = lo % base_mod, add = (base_res + base_mod - rem) % base_mod;
    if (add >= hi - lo)
      return;
    Coord x = lo + add;
    if (L.empty()) {
      for (;;) { out.push_back(x); if (base_mod >= hi-x) break; x+=base_mod; }
    } else if (L.size()==6) rec6<0>(x,hi,out,L[0].fm.mod128(x));
    else generic(0,x,hi,out);
  }
  template <typename Coord>
  void generate(Coord lo,Coord hi,std::vector<Coord>& out) const {
    while(lo<hi) {
      Coord end=lo+std::min(hi-lo,(Coord)period);
      generate_segment(lo,end,out);
      lo=end;
    }
  }
};
template <typename Coord> struct RadixScratch {
  // Sort chunk-relative offsets.  Default spans are <2^34, so this needs
  // only three 12-bit passes and a 16 KiB count table instead of the old
  // 3--4 passes with a 256 KiB/thread 16-bit count table.
  static constexpr unsigned RB = 12, RN = 1u << RB, RM = RN - 1;
  std::vector<Coord> tmp;
  std::vector<uint32_t> cnt = std::vector<uint32_t>(RN);
  void pass(std::vector<Coord> &a, Coord base, unsigned sh) {
    std::fill(cnt.begin(), cnt.end(), 0);
    for (Coord x : a)
      ++cnt[((x - base) >> sh) & RM];
    uint32_t s = 0;
    for (auto &c : cnt) {
      auto z = c;
      c = s;
      s += z;
    }
    for (Coord x : a)
      tmp[cnt[((x - base) >> sh) & RM]++] = x;
    a.swap(tmp);
  }
  void sort(std::vector<Coord> &a, Coord lo, Coord hi) {
    if (a.size() < 2)
      return;
    if (a.size() > UINT32_MAX)
      throw std::runtime_error("too many coordinates in one chunk; decrease chunk size");
    tmp.resize(a.size());
    Coord span = hi - lo;
    unsigned bits = bit_length_u128(span);
    for (unsigned sh = 0; sh < bits; sh += RB)
      pass(a, lo, sh);
  }
};

static std::vector<int> group_sizes(size_t n) {
  std::vector<int> v;
  size_t slots=std::min<size_t>(6,n);
  while (n) { int k=(n>slots ? 2 : 1); v.push_back(k); n-=k; --slots; }
  return v;
}
struct Config {
  std::string name;
  u64 bm, cls;
  bool reject_sq;
  std::vector<int> A, B;
  u64 Mp, Mn;
  Wheel wa, wb;
  Config(std::string nm, u64 base, u64 cl, std::vector<int> a,
         std::vector<int> b, bool rs)
      : name(std::move(nm)), bm(base), cls(cl), reject_sq(rs), A(std::move(a)),
        B(std::move(b)), Mp([&] {
          u64 z = 1;
          for (int p : A) {
            u128 t = (u128)z * p;
            if (t > UMAX)
              std::abort();
            z = (u64)t;
          }
          return z;
        }()),
        Mn([&] {
          u64 z = base;
          for (int p : B) {
            u128 t = (u128)z * p;
            if (t > UMAX)
              std::abort();
            z = (u64)t;
          }
          return z;
        }()),
        wa(
            1, 0, A,
            [&] {
              std::vector<int> s;
              for (int p : A)
                s.push_back(legendre(Mn, p));
              return s;
            }(),
            group_sizes(A.size())),
        wb(
            base, (base - (cl * inv_mod(Mp, base)) % base) % base, B,
            [&] {
              std::vector<int> s;
              for (int p : B)
                s.push_back(legendre((u64(p) - Mp % u64(p)) % u64(p), p));
              return s;
            }(),
            group_sizes(B.size())) {}
};

struct Opt {
  unsigned th = std::max(1u, std::thread::hardware_concurrency());
  u64 chunk = 1ULL << 20;
  u64 begin = 0, end = ~u64(0), progress = 1000;
  unsigned checkpoint_sec = 30;
  std::string mode = "odd", work = "work", csv = "unused.csv";
  bool fresh = false, merge_only = false, no_merge = true, verify_all = false, self_test = false;
};
static Opt parse(int ac, char **av) {
  Opt o;
  for (int i = 1; i < ac; i++) {
    std::string a = av[i];
    auto need = [&]() {
      if (++i >= ac) {
        std::cerr << "missing value after " << a << "\n";
        exit(2);
      }
      return std::string(av[i]);
    };
    if(a=="--non-one") NON_ONE=true;
    else if(a=="--wheel-limit") WHEEL_LIMIT=stoi(need());
    else if(a=="--root-prime") ROOT_PRIME=stoi(need());
    else if(a=="--root-exponent") ROOT_EXP=stoi(need());
    else if(a=="--upper-exclusive") {
      std::string v=need();
      size_t first=v.find_first_not_of('0');
      if(first!=std::string::npos) v.erase(0,first);
      FULL_LIMIT=(v==TWO128); HAS_LIMIT=true;
      LIMIT=FULL_LIMIT?0:parse_u128(v);
      if(!FULL_LIMIT && LIMIT<16) throw std::runtime_error("upper bound too small");
    }
    else if (a == "--bits") { BITS=stoul(need()); if(BITS<4 || BITS>128) throw std::runtime_error("bits must be 4..128"); }
    else if (a == "--lower") N_MIN=parse_u128(need());
    else if (a == "--threshold") { THRESHOLD=stoi(need()); if(THRESHOLD<3 || THRESHOLD>997 || !is_prime_small(THRESHOLD)) throw std::runtime_error("threshold must be an odd prime <=997"); }
    else if (a == "--self-test") o.self_test=true;
    else if (a == "--threads")
      o.th = stoul(need());
    else if (a == "--chunk-size")
      o.chunk = stoull(need());
    else if (a == "--chunk-begin")
      o.begin = stoull(need());
    else if (a == "--chunk-end")
      o.end = stoull(need());
    else if (a == "--progress-every")
      o.progress = stoull(need());
    else if (a == "--checkpoint-seconds")
      o.checkpoint_sec = stoul(need());
    else if (a == "--mode")
      o.mode = need();
    else if (a == "--work-dir")
      o.work = need();
    else if (a == "--csv")
      o.csv = need();
    else if (a == "--fresh")
      o.fresh = true;
    else if (a == "--merge-only")
      o.merge_only = true;
    else if (a == "--no-merge")
      o.no_merge = true;
    else if (a == "--verify-all")
      o.verify_all = true;
    else {
      std::cerr << "bad option " << a << "\n";
      exit(2);
    }
  }
  if(o.fresh) throw std::runtime_error("--fresh disabled; use a new work directory");
  if(o.mode!="odd") throw std::runtime_error("only odd mode supported");
  if(!o.th || !o.chunk) throw std::runtime_error("threads and chunk must be positive");
  N_HI=HAS_LIMIT?LIMIT:(BITS==128?0:((u128)1<<BITS)); N_MAX=N_HI-1;
  OUTPUT_HI=N_HI;
  OUTPUT_LO=N_MIN;
  if(N_MIN<1 || N_MIN>N_MAX) throw std::runtime_error("lower bound must be in 1..upper-1");
  if(NON_ONE && ROOT_PRIME) throw std::runtime_error("non-one does not use quotient branches");
  if(ROOT_PRIME) {
    if(ROOT_PRIME>=241 || !is_prime_small(ROOT_PRIME) || ROOT_PRIME==2 || (ROOT_EXP!=1 && ROOT_EXP!=2))
      throw std::runtime_error("root must be an odd prime below 241; exponent 1 or 2");
    MULTIPLIER=ROOT_EXP==1?ROOT_PRIME:(u64)ROOT_PRIME*ROOT_PRIME;
    N_MAX=(OUTPUT_HI-1)/MULTIPLIER; N_HI=N_MAX+1;
    N_MIN=(OUTPUT_LO-1)/MULTIPLIER+1;
  } else if(ROOT_EXP) throw std::runtime_error("exponent requires root prime");
  FILTER_LIMIT=std::max(THRESHOLD-1,ROOT_PRIME);
  for(int q:odd_primes_upto(FILTER_LIMIT)) COEFFICIENT_SYMBOL[q]=legendre(MULTIPLIER,q);
  BITS=bit_length_u128(N_MAX);
  return o;
}

struct BinRec {
  u64 lo, hi;
};
static BinRec split128(u128 x) { return BinRec{(u64)x, (u64)(x >> 64)}; }
static u128 join128(BinRec r) { return ((u128)r.hi << 64) | r.lo; }

struct Bitmap {
  u64 nbits = 0, nwords = 0;
  std::unique_ptr<std::atomic<u64>[]> w;
  explicit Bitmap(u64 n = 0)
      : nbits(n), nwords(n / 64 + (n % 64 != 0)),
        w(nwords ? new std::atomic<u64>[nwords] : nullptr) {
    for (u64 i = 0; i < nwords; i++)
      w[i].store(0);
  }
  bool test(u64 i) const {
    return (w[i >> 6].load(std::memory_order_relaxed) >> (i & 63)) & 1ULL;
  }
  void set(u64 i) {
    w[i >> 6].fetch_or(1ULL << (i & 63), std::memory_order_relaxed);
  }
  u64 count() const {
    u64 s = 0;
    for (u64 i = 0; i < nwords; i++)
      s += __builtin_popcountll(w[i].load(std::memory_order_relaxed));
    return s;
  }
};

struct BitmapHeader {
  char magic[8];
  u64 version, total, chunk, width, Mp, Mn, bm, cls;
  u64 nmax_hi, nmax_lo;
};
static constexpr char BM_MAGIC[8] = {'N', 'E', 'G', 'R', 'B', 'M', '1', '\0'};

static void save_bitmap(const fs::path &path, const Bitmap &bm,
                        const BitmapHeader &h) {
  fs::create_directories(path.parent_path());
  fs::path tmp = path;
  tmp += ".tmp";
  std::ofstream f(tmp, std::ios::binary | std::ios::trunc);
  if (!f)
    throw std::runtime_error("cannot write bitmap tmp");
  f.write((const char *)&h, sizeof(h));
  for (u64 i = 0; i < bm.nwords; i++) {
    u64 x = bm.w[i].load(std::memory_order_relaxed);
    f.write((const char *)&x, sizeof(x));
  }
  f.flush();
  f.close();
  if(!f) throw std::runtime_error("bitmap write/flush failure");
  std::error_code ec;
  fs::remove(path, ec);
  fs::rename(tmp, path);
}
static bool load_bitmap(const fs::path &path, Bitmap &bm,
                        const BitmapHeader &expect) {
  std::ifstream f(path, std::ios::binary);
  if (!f)
    return false;
  BitmapHeader h{};
  f.read((char *)&h, sizeof(h));
  if (!f || std::memcmp(h.magic, BM_MAGIC, 8) != 0 ||
      h.version != expect.version || h.total != expect.total ||
      h.chunk != expect.chunk || h.width != expect.width || h.Mp != expect.Mp ||
      h.Mn != expect.Mn || h.bm != expect.bm || h.cls != expect.cls ||
      h.nmax_hi != expect.nmax_hi || h.nmax_lo != expect.nmax_lo) {
    throw std::runtime_error("checkpoint metadata mismatch for " +
                             path.string());
  }
  for (u64 i = 0; i < bm.nwords; i++) {
    u64 x = 0;
    f.read((char *)&x, sizeof(x));
    if (!f)
      throw std::runtime_error("truncated bitmap");
    bm.w[i].store(x);
  }
  return true;
}

// Fixed shard count is independent of both chunk count and worker count.
static constexpr unsigned RESULT_SHARDS = 16;
static constexpr u64 MAX_RESULT_BYTES = 64ULL << 20;
static fs::path result_path(const fs::path &dir, unsigned shard) {
  return dir / ("results-" + std::to_string(shard) + ".journal");
}
static void put_le64(char *p, u64 x) {
  for (unsigned i = 0; i < 8; ++i) p[i] = char(x >> (8 * i));
}
static u64 get_le64(const char *p) {
  u64 x = 0;
  for (unsigned i = 0; i < 8; ++i) x |= u64((unsigned char)p[i]) << (8 * i);
  return x;
}
static u64 result_hash(const char *metadata, const std::string &payload) {
  u64 h = 14695981039346656037ULL;
  for (unsigned i = 0; i < 16; ++i) h = (h ^ (unsigned char)metadata[i]) * 1099511628211ULL;
  for (unsigned char c : payload) h = (h ^ c) * 1099511628211ULL;
  return h;
}
static void recover_results(const fs::path &dir, Bitmap &bm, u64 total) {
  for (const auto &entry : fs::directory_iterator(dir))
    if (entry.path().filename().string().rfind("chunk-", 0) == 0)
      throw std::runtime_error("legacy chunk CSV work directory; use a new work directory");
  // Journals are authoritative. A crash may leave the bitmap missing or stale.
  for (u64 i = 0; i < bm.nwords; ++i) bm.w[i].store(0);
  for (unsigned shard = 0; shard < RESULT_SHARDS; ++shard) {
    fs::path path = result_path(dir, shard);
    if (!fs::exists(path)) continue;
    std::ifstream in(path, std::ios::binary);
    if (!in) throw std::runtime_error("cannot read result journal");
    u64 valid = 0;
    for (;;) {
      char header[32];
      in.read(header, sizeof(header));
      auto got = in.gcount();
      if (got == 0 && in.eof()) break;
      if (got != sizeof(header)) {
        if (!in.eof()) throw std::runtime_error("result journal read failure");
        in.close(); fs::resize_file(path, valid); break;
      }
      u64 ci = get_le64(header + 8), size = get_le64(header + 16);
      if (std::memcmp(header, "QWJNL001", 8) || ci >= total ||
          ci % RESULT_SHARDS != shard || size > MAX_RESULT_BYTES)
        throw std::runtime_error("invalid result journal header");
      std::string payload(size, '\0');
      in.read(payload.data(), size);
      if ((u64)in.gcount() != size) {
        if (!in.eof()) throw std::runtime_error("result journal read failure");
        in.close(); fs::resize_file(path, valid); break;
      }
      if (get_le64(header + 24) != result_hash(header + 8, payload))
        throw std::runtime_error("result journal checksum mismatch");
      if (bm.test(ci)) throw std::runtime_error("duplicate result journal chunk");
      bm.set(ci);
      valid += sizeof(header) + size;
    }
  }
}

static std::pair<int, int> first_bad(u128 n,
                                     const std::vector<FirstFailGroup> &tail) {
  for (auto const &g : tail) {
    uint8_t c = g.classify(n);
    if (c)
      return {g.prime_of(c), g.chi_of(c)};
  }
  int p = tail.empty()?THRESHOLD:tail.back().ps.back()+2;
  while (!is_prime_small(p))
    p += 2;
  for (;; p = next_odd_prime(p)) {
    int c = legendre128(n, p);
    if (NON_ONE ? c != 1 : c == -1)
      return {p, c};
  }
}

struct RunStats {
  std::atomic<unsigned long long> pairs{0}, norm1{0}, stage2{0}, survivors{0};
  std::atomic<u64> chunks{0};
};

// A short interval near a large lower bound can have a huge CRT-coordinate
// envelope even though it contains few inputs. Scan that interval directly;
// this avoids enumerating empty CRT chunks when extending a completed prefix.
static bool run_direct_range(const Config &C, const Opt &O,
                             const std::vector<FirstFailGroup> &tail) {
  fs::path mdir = fs::path(O.work) / C.name;
  fs::create_directories(mdir);
  fs::path marker = mdir / "direct.range";
  if (fs::exists(marker)) {
    std::ifstream existing(marker);
    std::string contents((std::istreambuf_iterator<char>(existing)), {});
    if (contents != "direct-range-v1\n")
      throw std::runtime_error("direct-range marker mismatch");
  } else {
    std::ofstream created(marker, std::ios::binary | std::ios::trunc);
    created << "direct-range-v1\n";
    created.flush();
    if (!created)
      throw std::runtime_error("cannot write direct-range marker");
  }
  Bitmap bm(1);
  BitmapHeader bh{};
  std::memcpy(bh.magic, BM_MAGIC, 8);
  bh.version = THRESHOLD + 1000 * ROOT_PRIME + 1000000 * ROOT_EXP;
  bh.total = 1;
  bh.chunk = O.chunk;
  bh.width = O.chunk;
  bh.Mp = C.Mp;
  bh.Mn = C.Mn;
  bh.bm = C.bm;
  bh.cls = C.cls;
  bh.nmax_hi = (u64)(N_MAX >> 64);
  bh.nmax_lo = (u64)N_MAX;
  if (!O.fresh)
    load_bitmap(mdir / "done.bitmap", bm, bh);
  recover_results(mdir, bm, 1);
  save_bitmap(mdir / "done.bitmap", bm, bh);
  if (bm.test(0))
    return true;

  std::vector<int> filter_primes = odd_primes_upto(FILTER_LIMIT);
  std::map<int, std::pair<u128, u128>> minima;
  u128 n = N_MIN;
  if (!(n & 1))
    ++n;
  for (;;) {
    if (g_stop || fs::exists(fs::path(O.work) / "stop.request")) {
      g_stop = true;
      return false;
    }
    bool pass = true;
    for (int p : filter_primes) {
      if (p >= THRESHOLD && p != ROOT_PRIME) {
        if (!ROOT_PRIME)
          break;
        continue;
      }
      if (!allow_m(p, legendre128(n, p))) {
        pass = false;
        break;
      }
    }
    if (pass && !ROOT_PRIME && C.reject_sq && (n & 7) == 1 &&
        is_square_u128(n))
      pass = false;
    if (pass) {
      u128 x = n * MULTIPLIER;
      int p = first_bad(x, tail).first;
      auto [it, inserted] = minima.try_emplace(p, std::pair<u128, u128>{x, 0});
      it->second.first = std::min(it->second.first, x);
      ++it->second.second;
    }
    if (N_MAX - n < 2)
      break;
    n += 2;
  }

  std::ostringstream rows;
  for (auto const &[p, row] : minima)
    rows << to_string_u128(row.first) << ',' << p << ','
         << to_string_u128(row.second) << '\n';
  std::string payload = rows.str();
  char header[32];
  std::memcpy(header, "QWJNL001", 8);
  put_le64(header + 8, 0);
  put_le64(header + 16, payload.size());
  put_le64(header + 24, result_hash(header + 8, payload));
  {
    std::ofstream result(result_path(mdir, 0), std::ios::binary | std::ios::app);
    result.write(header, sizeof(header));
    result.write(payload.data(), payload.size());
    result.flush();
    result.close();
    if (!result)
      throw std::runtime_error("direct-range result write failure");
  }
  bm.set(0);
  save_bitmap(mdir / "done.bitmap", bm, bh);
  std::cerr << '[' << C.name << "] direct range complete; witness classes="
            << minima.size() << "\n";
  return true;
}

template <typename Coord> static bool run_mode(const Config &C, const Opt &O,
                     const std::array<CoordGroup, 3> &coord,
                     const std::vector<PassGroup> &groups,
                     const std::vector<FirstFailGroup> &tail) {
  u128 wide_width = ((u128)O.chunk * C.Mp + C.wa.residue_count - 1) /
                    C.wa.residue_count;
  if (!wide_width || wide_width > UMAX)
    throw std::runtime_error("chunk width exceeds 64 bits; decrease chunk size");
  u64 width = (u64)wide_width;
  Coord tp_begin = (Coord)(N_MIN / C.Mn);
  Coord tp_end = (Coord)(N_MAX / C.Mn + C.Mp + 2);
  u128 wide_total = (u128)(tp_end - tp_begin) / width + ((tp_end - tp_begin) % width != 0);
  if (wide_total > UMAX - O.th)
    throw std::runtime_error("chunk count exceeds 64 bits; increase threshold or restrict --lower");
  u64 total = (u64)wide_total;
  u64 be = std::min(O.begin, total), en = std::min(O.end, total);
  fs::path mdir = fs::path(O.work) / C.name;
  fs::create_directories(mdir);
  fs::path bmpath = mdir / "done.bitmap";
  Bitmap bm(total);
  BitmapHeader bh{};
  std::memcpy(bh.magic, BM_MAGIC, 8);
  bh.version = THRESHOLD+1000*ROOT_PRIME+1000000*ROOT_EXP;
  bh.total = total;
  bh.chunk = O.chunk;
  bh.width = width;
  bh.Mp = C.Mp;
  bh.Mn = C.Mn;
  bh.bm = C.bm;
  bh.cls = C.cls;
  bh.nmax_hi = (u64)(N_MAX >> 64);
  bh.nmax_lo = (u64)N_MAX;
  if (!O.fresh)
    load_bitmap(bmpath, bm, bh);
  else {
    std::error_code ec;
    fs::remove_all(mdir, ec);
    fs::create_directories(mdir);
  }

  recover_results(mdir, bm, total);
  save_bitmap(bmpath,bm,bh);
  u64 initial_done = 0;
  for (u64 i = be; i < en; i++)
    if (bm.test(i))
      ++initial_done;
  std::cerr << "[" << C.name << "] " << (NON_ONE ? "non_one" : "negative")
            << " n<" << upper_exclusive_text()
            << " threshold=" << THRESHOLD << " Mp=" << C.Mp << " Mn=" << C.Mn
            << " width=" << width << " chunks=" << total << " run=[" << be
            << "," << en << ") chunkA=" << O.chunk << " threads=" << O.th
            << " resumed=" << initial_done << "\n";

  if (O.merge_only)
    return initial_done == (en - be);

  struct WS {
    std::map<int,std::pair<u128,u128>> minima; // witness -> (least n, count)
  };
  std::vector<WS> ws(O.th);
  std::shared_mutex commit_mu;
  std::mutex log_mu;
  std::array<std::mutex, RESULT_SHARDS> result_mu;
  std::atomic<u64> next{be};
  RunStats st;
  st.chunks.store(initial_done);
  auto t0 = std::chrono::steady_clock::now();

  auto checkpoint = [&](const char *why) {
    std::unique_lock lk(commit_mu);
    save_bitmap(bmpath, bm, bh);
    std::lock_guard lg(log_mu);
    std::cerr << "[" << C.name << "] checkpoint(" << why
              << ") done=" << st.chunks.load() << "/" << (en - be)
              << " bitmap_total=" << bm.count() << "\n";
  };

  // CRT-strip constants shared by every worker/chunk.  rem_recip is a
  // floor 64-bit reciprocal. For every u64 d, high64(d*rem_recip)
  // underestimates floor(d*remp/Mn) by at most one; adding rr<Mn
  // needs at most one further carry. This avoids u128/u64 division in
  // the per-tn loop.
  const u64 strip_q0 = C.Mp / C.Mn, strip_remp = C.Mp % C.Mn;
  const u64 strip_recip = (u64)(((u128)strip_remp << 64) / C.Mn);
  const Coord strip_UK = (Coord)(N_MAX / C.Mn), strip_LK = (Coord)(N_MIN / C.Mn);
  const u64 strip_Urem = (u64)(N_MAX % C.Mn), strip_Lrem = (u64)(N_MIN % C.Mn);
  const u64 strip_Uthreshold = C.Mn - strip_Urem;

  std::atomic<bool> cp_stop{false};
  // --checkpoint-seconds 0 disables the periodic checkpoint thread.  This is
  // useful for reproducible short benchmarks; the final checkpoint is still
  // written normally.
  std::jthread cpthread;
  if (O.checkpoint_sec) {
    cpthread = std::jthread([&] {
      while (!cp_stop.load()) {
        for (unsigned s = 0; s < O.checkpoint_sec && !cp_stop.load(); s++)
          std::this_thread::sleep_for(std::chrono::seconds(1));
        if (!cp_stop.load())
          checkpoint("timer");
      }
    });
  }

  auto worker = [&](unsigned tid) {
    std::vector<Coord> a;
    std::vector<u64> b;
    std::vector<uint32_t> key0;
    RadixScratch<Coord> rs;
    RadixScratch<u64> bsort;
    auto &minima = ws[tid].minima;
    a.reserve(O.chunk + O.chunk / 4 + 1024);
    key0.reserve(O.chunk + O.chunk / 4 + 1024);
    b.reserve(O.chunk * 2 + 1024);
    for (;;) {
      if (fs::exists(fs::path(O.work)/"stop.request")) g_stop=true;
      if (g_stop) break;
      u64 ci = next.fetch_add(1);
      if (ci >= en)
        break;
      if (bm.test(ci))
        continue;
      Coord lo = tp_begin + (Coord)ci * width;
      Coord hi = lo + std::min(tp_end - lo, (Coord)width);

      // B first. After the subsequent A radix sort, rs.tmp is no longer
      // needed as scratch and is reused as the packed coordinate array.
      u64 tnlo = 0;
      if (lo > strip_UK) {
        // Subtract the upper quotient first. The remaining product is at
        // most (Mp+1)*Mn, even when lo*Mn itself would exceed 2^128.
        u128 diff = (u128)(lo - strip_UK) * C.Mn - strip_Urem;
        tnlo = (u64)std::min((u128)C.Mn, diff / C.Mp + (diff % C.Mp != 0));
      }
      u64 tnhi = 0;
      if (hi - 1 >= strip_LK) {
        Coord delta = hi - 1 - strip_LK;
        if (delta > C.Mp) tnhi = C.Mn;
        else if ((u128)delta * C.Mn >= strip_Lrem) {
          u128 diff = (u128)delta * C.Mn - strip_Lrem;
          tnhi = (u64)std::min((u128)C.Mn, diff / C.Mp + 1);
        }
      }
      b.clear();
      if (tnlo < tnhi)
        C.wb.generate(tnlo, tnhi, b);
      if (!b.empty())
        bsort.sort(b, tnlo, tnhi - 1);

      a.clear();
      C.wa.generate(lo, hi, a);
      rs.sort(a, lo, hi - 1);

      std::vector<u64> &key12 = [&]() -> std::vector<u64>& {
        if constexpr (std::is_same_v<Coord, u64>) return rs.tmp;
        else return bsort.tmp;
      }();
      key0.resize(a.size());
      key12.resize(a.size());
      for (size_t j = 0; j < a.size(); j++) {
        key0[j] = coord[0].akey(a[j]);
        key12[j] = (u64)coord[1].akey(a[j]) | ((u64)coord[2].akey(a[j]) << 21);
      }

      size_t li = 0, ri = 0;
      u64 prev_tn = 0, qr = 0, rr = 0;
      bool have = false;
      unsigned long long lp = 0, l1 = 0, l2 = 0, ls = 0;
      minima.clear();
      auto accept = [&](u128 x) {
        x*=MULTIPLIER;
        int p=first_bad(x,tail).first;
        auto [it,inserted]=minima.try_emplace(p,std::pair<u128,u128>{x,0});
        it->second.first=std::min(it->second.first,x);
        ++it->second.second;
      };
      for (u64 tn : b) {
        if (!have) {
          u128 zz = (u128)tn * C.Mp;
          qr = (u64)(zz / C.Mn);
          rr = (u64)(zz % C.Mn);
          have = true;
        } else {
          u64 d = tn - prev_tn;
          if (strip_remp == 0) {
            qr += d * strip_q0;
            rr = 0;
          } else {
            u64 cq = (u64)(((u128)d * strip_recip) >> 64);
            u128 v = (u128)rr + (u128)d * strip_remp;
            u128 diff = v - (u128)cq * C.Mn;
            if (diff >= C.Mn) {
              diff -= C.Mn;
              ++cq;
            }
            if (diff >= C.Mn) {
              diff -= C.Mn;
              ++cq;
            }
            qr += d * strip_q0 + cq;
            rr = (u64)diff;
          }
        }
        prev_tn = tn;
        Coord tmin = (Coord)qr + strip_LK +
            (Coord)(((u128)strip_Lrem + rr + C.Mn - 1) / C.Mn);
        Coord tmax = (Coord)qr + strip_UK + (rr >= strip_Uthreshold ? 1u : 0u);
        if (tmin < lo)
          tmin = lo;
        if (tmax >= hi)
          tmax = hi - 1;
        if (tmin > tmax)
          continue;
        while (li < a.size() && a[li] < tmin)
          ++li;
        if (ri < li)
          ri = li;
        while (ri < a.size() && a[ri] <= tmax)
          ++ri;
        lp += (unsigned long long)(ri - li);
        if (li == ri)
          continue;
        const uint32_t cb0 = coord[0].bkey(tn), cb1 = coord[1].bkey(tn),
                       cb2 = coord[2].bkey(tn);
        size_t j = li;
        const u64 cb = cb0, mm = coord[0].m;
        bool zhave = false;
        u128 zlo = 0;
        auto finish_mask = [&](unsigned mask, size_t basej) {
          while (mask) {
            unsigned lane = __builtin_ctz(mask);
            mask &= mask - 1;
            size_t jj = basej + lane;
            u64 pk = key12[jj];
            bool ok = true;
            if (__builtin_expect(
                    !coord[1].pass((uint32_t)(pk & ((1u << 21) - 1)), cb1), 1))
              continue;
            if (__builtin_expect(!coord[2].pass((uint32_t)(pk >> 21), cb2), 1))
              continue;
            ++l1;
            if (!zhave) {
              zlo = (u128)tn * C.Mp;
              zhave = true;
            }
            // Modular wrap of the product is harmless: the CRT strip above
            // has already proved that the difference lies in [N_MIN,N_MAX].
            u128 x = (u128)a[jj] * C.Mn - zlo;
            for (auto const &g : groups)
              if (!g(x)) {
                ok = false;
                break;
              }
            if (!ok)
              continue;
            ++l2;
            if (!ROOT_PRIME && C.reject_sq && (x & 7) == 1 && is_square_u128(x))
              continue;
            accept(x);
            ++ls;
          }
        };
        for (; j + 8 <= ri; j += 8) {
          u64 r0 = key0[j], r1 = key0[j + 1], r2 = key0[j + 2],
              r3 = key0[j + 3];
          u64 r4 = key0[j + 4], r5 = key0[j + 5], r6 = key0[j + 6],
              r7 = key0[j + 7];
          r0 = (r0 >= cb) ? r0 - cb : r0 + mm - cb;
          r1 = (r1 >= cb) ? r1 - cb : r1 + mm - cb;
          r2 = (r2 >= cb) ? r2 - cb : r2 + mm - cb;
          r3 = (r3 >= cb) ? r3 - cb : r3 + mm - cb;
          r4 = (r4 >= cb) ? r4 - cb : r4 + mm - cb;
          r5 = (r5 >= cb) ? r5 - cb : r5 + mm - cb;
          r6 = (r6 >= cb) ? r6 - cb : r6 + mm - cb;
          r7 = (r7 >= cb) ? r7 - cb : r7 + mm - cb;
          const u64 *bp = coord[0].bits.data();
          u64 w0 = bp[r0 >> 6], w1 = bp[r1 >> 6], w2 = bp[r2 >> 6],
              w3 = bp[r3 >> 6];
          u64 w4 = bp[r4 >> 6], w5 = bp[r5 >> 6], w6 = bp[r6 >> 6],
              w7 = bp[r7 >> 6];
          unsigned mask = 0;
          mask |= (unsigned)((w0 >> (r0 & 63)) & 1u) << 0;
          mask |= (unsigned)((w1 >> (r1 & 63)) & 1u) << 1;
          mask |= (unsigned)((w2 >> (r2 & 63)) & 1u) << 2;
          mask |= (unsigned)((w3 >> (r3 & 63)) & 1u) << 3;
          mask |= (unsigned)((w4 >> (r4 & 63)) & 1u) << 4;
          mask |= (unsigned)((w5 >> (r5 & 63)) & 1u) << 5;
          mask |= (unsigned)((w6 >> (r6 & 63)) & 1u) << 6;
          mask |= (unsigned)((w7 >> (r7 & 63)) & 1u) << 7;
          finish_mask(mask, j);
        }
        for (; j < ri; j++) {
          bool ok = true;
          if (__builtin_expect(!coord[0].pass(key0[j], cb0), 1))
            continue;
          u64 pk = key12[j];
          if (__builtin_expect(
                  !coord[1].pass((uint32_t)(pk & ((1u << 21) - 1)), cb1), 1))
            continue;
          if (__builtin_expect(!coord[2].pass((uint32_t)(pk >> 21), cb2), 1))
            continue;
          ++l1;
          if (!zhave) {
            zlo = (u128)tn * C.Mp;
            zhave = true;
          }
          u128 x = (u128)a[j] * C.Mn - zlo;
          for (auto const &g : groups)
            if (!g(x)) {
              ok = false;
              break;
            }
          if (!ok)
            continue;
          ++l2;
          if (!ROOT_PRIME && C.reject_sq && (x & 7) == 1 && is_square_u128(x))
            continue;
          accept(x);
          ++ls;
        }
      }

      // A checksummed frame commits a whole chunk, including empty results.
      // Flush before setting its bit; recovery rebuilds bits from complete frames.
      std::ostringstream rows;
      for (auto const &[p, row] : minima)
        rows << to_string_u128(row.first) << ',' << p << ','
             << to_string_u128(row.second) << '\n';
      std::string payload = rows.str();
      if (payload.size() > MAX_RESULT_BYTES)
        throw std::runtime_error("result frame too large");
      char header[32];
      std::memcpy(header, "QWJNL001", 8);
      put_le64(header + 8, ci); put_le64(header + 16, payload.size());
      put_le64(header + 24, result_hash(header + 8, payload));
      std::shared_lock lk(commit_mu);
      {
        unsigned shard = ci % RESULT_SHARDS;
        std::lock_guard guard(result_mu[shard]);
        std::ofstream result(result_path(mdir, shard), std::ios::binary | std::ios::app);
        result.write(header, sizeof(header));
        result.write(payload.data(), payload.size());
        result.flush(); result.close();
        if (!result) throw std::runtime_error("result journal write/flush failure");
      }
      bm.set(ci);
      lk.unlock();
      st.pairs.fetch_add(lp, std::memory_order_relaxed);
      st.norm1.fetch_add(l1, std::memory_order_relaxed);
      st.stage2.fetch_add(l2, std::memory_order_relaxed);
      st.survivors.fetch_add(ls, std::memory_order_relaxed);
      u64 d = st.chunks.fetch_add(1) + 1;
      if (O.progress && d % O.progress == 0) {
        double sec =
            std::chrono::duration<double>(std::chrono::steady_clock::now() - t0)
                .count();
        std::lock_guard lg(log_mu);
        std::cerr << "[" << C.name << "] " << d << "/" << (en - be)
                  << " chunks " << (d - initial_done) / sec
                  << " new-ch/s pairs=" << st.pairs.load()
                  << " coord8=" << st.norm1.load()
                  << " pass_before_threshold=" << st.stage2.load()
                  << " nonsquare=" << st.survivors.load() << "\n";
      }
    }
  };

  std::vector<std::jthread> pool;
  for (unsigned t = 0; t < O.th; t++)
    pool.emplace_back(worker, t);
  pool.clear();
  cp_stop.store(true);
  if (cpthread.joinable())
    cpthread.join();
  checkpoint(g_stop ? "signal" : "final");
  double sec =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - t0)
          .count();
  u64 done_range = 0;
  for (u64 i = be; i < en; i++)
    if (bm.test(i))
      ++done_range;
  std::cerr << "[" << C.name << "] stop done=" << done_range << "/" << (en - be)
            << " new_pairs=" << st.pairs.load() << " coord8=" << st.norm1.load()
            << " pass_before_threshold=" << st.stage2.load()
            << " nonsquare=" << st.survivors.load() << " sec=" << sec << "\n";
  return done_range == (en - be);
}

static void merge_output(const Opt &O, const std::vector<std::string> &modes,
                         const std::vector<FirstFailGroup> &tail) {
  std::vector<u128> v;
  for (auto const &mode : modes) {
    fs::path d = fs::path(O.work) / mode;
    if (!fs::exists(d))
      continue;
    for (auto const &e : fs::directory_iterator(d)) {
      if (!e.is_regular_file())
        continue;
      auto s = e.path().filename().string();
      if (s.rfind("shard-", 0) != 0 || e.path().extension() != ".bin")
        continue;
      std::ifstream f(e.path(), std::ios::binary);
      BinRec r;
      while (f.read((char *)&r, sizeof(r)))
        v.push_back(join128(r));
    }
  }
  std::cerr << "[merge] raw records=" << v.size() << "\n";
  std::sort(v.begin(), v.end());
  v.erase(std::unique(v.begin(), v.end()), v.end());
  std::cerr << "[merge] unique=" << v.size() << "\n";
  std::ofstream out(O.csv);
  if (!out)
    throw std::runtime_error("cannot open csv");
  out << "n,bit_length,first_bad_prime,legendre\n";
  auto prior = odd_primes_upto(239);
  u64 verified = 0;
  for (u128 n : v) {
    if (!(n >= N_MIN && n <= N_MAX && (n & 1) && !is_square_u128(n)))
      throw std::runtime_error("bad merged survivor");
    if (O.verify_all) {
      for (int p : prior)
        if (legendre128(n, p) != 1) {
          std::cerr << "VERIFY FAIL n=" << to_string_u128(n) << " p=" << p
                    << "\n";
          std::abort();
        }
    }
    auto [p, c] = first_bad(n, tail);
    out << to_string_u128(n) << ',' << bit_length_u128(n) << ',' << p << ','
        << c << '\n';
    ++verified;
  }
  std::cerr << "[merge] wrote " << verified << " rows to " << O.csv
            << (O.verify_all ? " (full p<241 verification)" : "") << "\n";
}

static int allowed_count(int p) {
  int count=0;
  for(int r=0;r<p;++r) count+=allow_m(p,legendre(r,p));
  return count;
}
static void partition_primes(int limit,std::vector<int>& A,std::vector<int>& B) {
  auto ps=odd_primes_upto(std::min(limit,FILTER_LIMIT));
  size_t capacity=(ps.size()+1)/2;
  long double ca=1,cb=1;
  for(auto it=ps.rbegin();it!=ps.rend();++it) {
    int p=*it;
    if(B.size()==capacity || (A.size()<capacity && ca<=cb)) {A.push_back(p);ca*=allowed_count(p);}
    else {B.push_back(p);cb*=allowed_count(p);}
  }
  std::sort(A.begin(),A.end());std::sort(B.begin(),B.end());
}
static int choose_limit() {
  if(WHEEL_LIMIT) {
    if(WHEEL_LIMIT<3 || WHEEL_LIMIT>73 || !is_prime_small(WHEEL_LIMIT))
      throw std::runtime_error("wheel limit must be an odd prime <=73");
    return WHEEL_LIMIT;
  }
  int best=17;
  long double cost=std::numeric_limits<long double>::infinity();
  for(int limit:std::vector<int>{17,19,23,29,31,37,41,43,47,53,59,61,67,71,73}) {
    std::vector<int> A,B;partition_primes(limit,A,B);
    long double ma=1,mb=2,ca=1,cb=1;
    for(int p:A) {ma*=p;ca*=allowed_count(p);}
    for(int p:B) {mb*=p;cb*=allowed_count(p);}
    long double pairs=(long double)N_MAX*ca*cb/(ma*mb);
    long double emissions=ca*(1+(long double)N_MAX/(ma*mb))+cb;
    long double proposal=pairs+4*emissions;
    if(proposal<cost) {cost=proposal;best=limit;}
  }
  return best;
}
static int search_main(int ac, char **av) {
  std::signal(SIGINT, on_signal);
#ifdef SIGTERM
  std::signal(SIGTERM, on_signal);
#endif
  Opt O = parse(ac, av);
  if (O.fresh) {
    std::error_code ec;
    fs::remove_all(O.work, ec);
  }
  fs::create_directories(O.work);
  const bool direct_range = OUTPUT_LO >= (u128(1) << 64) &&
      OUTPUT_HI > OUTPUT_LO && OUTPUT_HI - OUTPUT_LO <= DIRECT_RANGE_MAX_SPAN;
  std::ostringstream description;
  description << "{\"result_format\":1,\"chunk_size\":" << O.chunk
    << ",\"wheel_limit\":" << WHEEL_LIMIT << ",\"non_one\":" << (NON_ONE ? "true" : "false") << ",\"threshold\":" << THRESHOLD << ",\"root_prime\":" << ROOT_PRIME
    << ",\"root_exponent\":" << ROOT_EXP << ",\"multiplier\":" << MULTIPLIER
    << ",\"lower_inclusive\":\"" << to_string_u128(OUTPUT_LO)
    << "\",\"upper_exclusive\":\"" << upper_exclusive_text() << "\"}\n";
  fs::path parameters=fs::path(O.work)/"branch.json";
  if(fs::exists(parameters)) {
    std::ifstream old(parameters); std::string contents((std::istreambuf_iterator<char>(old)),{});
    if(contents!=description.str()) throw std::runtime_error("branch configuration mismatch");
  } else {
    std::ofstream meta(parameters); meta<<description.str(); meta.flush();meta.close();
    if(!meta) throw std::runtime_error("cannot write branch metadata");
  }

  // Bound-dependent wheel keeps small verification runs affordable.
  int limit=choose_limit();
  std::cerr<<"wheel-limit="<<limit<<" root="<<ROOT_PRIME<<" exponent="<<ROOT_EXP<<" original n<"<<upper_exclusive_text()<<"\n";
  std::vector<int> A,B;
  partition_primes(limit,A,B);
  std::vector<PassGroup> groups;
  auto all_primes=odd_primes_upto(FILTER_LIMIT);
  // In the production wheel (<=73), coordinate groups cover 79..113.
  // Smaller wheels need the missing primes as additional ordinary filters.
  for(int p:all_primes) if(p>limit && !(p==79||p==83||p==89||p==97||p==101||p==103||p==107||p==109||p==113))
    groups.emplace_back(std::vector<int>{p});
  std::vector<FirstFailGroup> tail;
  std::vector<int> tail_primes;
  for(int p=THRESHOLD;tail_primes.size()<16;p+=2) if(is_prime_small(p)) tail_primes.push_back(p);
  for(size_t i=0;i<tail_primes.size();i+=2)
    tail.emplace_back(std::vector<int>{tail_primes[i],tail_primes[i+1]});

  bool all_complete = true;
  std::vector<std::string> selected;
  auto run = [&](Config &c) {
    // Keep the first highly selective 3-prime group unchanged.  For the
    // remaining five coordinate primes, test a 3-prime group before the
    // final 2-prime group; this reduces the number of second lookups/branches.
    std::array<CoordGroup, 3> coord = {
        CoordGroup(std::vector<int>{79, 83, 89}, c.Mp, c.Mn),
        CoordGroup(std::vector<int>{97, 101, 103}, c.Mp, c.Mn),
        CoordGroup(std::vector<int>{107, 109, 113}, c.Mp, c.Mn)};
    if(O.self_test) {
      auto check_wheel=[&](Wheel const& w,std::vector<int> const& ps,u64 coefficient) {
        for(u64 lo:std::vector<u64>{0,12345,w.period-1,w.period+12345}) {
          u64 hi=lo+10000;
          std::vector<u64> got,expected;
          w.generate(lo,hi,got); std::sort(got.begin(),got.end());
          for(u64 x=lo;x<hi;++x) {
            if(x%w.base_mod!=w.base_res) continue;
            bool pass=true;
            for(int p:ps) {
              int value=legendre(x,p);
              if(!allow_m(p,value*legendre(coefficient,p))) {pass=false;break;}
            }
            if(pass) expected.push_back(x);
          }
          if(got!=expected) throw std::runtime_error("wheel self-test mismatch");
        }
      };
      check_wheel(c.wa,c.A,c.Mn);
      // B wants (-Mp/p); represent the negative coefficient modulo each p.
      for(u64 lo:std::vector<u64>{0,12345,c.wb.period-1,c.wb.period+12345}) {
        std::vector<u64> got,expected;
        c.wb.generate(lo,lo+10000,got); std::sort(got.begin(),got.end());
        for(u64 x=lo;x<lo+10000;++x) {
          if(x%c.bm!=c.wb.base_res) continue;
          bool pass=true;
          for(int p:c.B) {
            int value=legendre(x,p),want=legendre((p-c.Mp%p)%p,p);
            if(!allow_m(p,value*want)) {pass=false;break;}
          }
          if(pass) expected.push_back(x);
        }
        if(got!=expected) throw std::runtime_error("B wheel self-test mismatch");
      }
      for(u64 tn:std::vector<u64>{0,1,99,c.Mn-1}) {
        u64 tp=(u64)(((u128)tn*c.Mp)/c.Mn)+1;
        for(u64 add:std::vector<u64>{0,1,10000,1000000}) {
          u128 n=(u128)(tp+add)*c.Mn-(u128)tn*c.Mp;
          for(auto const& g:coord) {
            bool expected=true;
            for(int p:g.ps) if(!allow_m(p,legendre128(n,p))) expected=false;
            if(g.pass(g.akey(tp+add),g.bkey(tn))!=expected)
              throw std::runtime_error("coordinate self-test mismatch");
          }
        }
      }
      std::cerr << "SELF TEST PASSED\n";
      return;
    }
    bool direct_this_job = direct_range;
    fs::path job_mode = fs::path(O.work) / c.name;
    if (direct_this_job && !fs::exists(job_mode / "direct.range")) {
      if (fs::exists(job_mode / "done.bitmap")) {
        direct_this_job = false;
      } else {
        for (unsigned shard = 0; shard < RESULT_SHARDS; ++shard)
          if (fs::exists(result_path(job_mode, shard)))
            direct_this_job = false;
      }
    }
    bool ok = direct_this_job
        ? run_direct_range(c, O, tail)
        : (N_MAX / c.Mn + c.Mp + 2 > UMAX
            ? run_mode<u128>(c, O, coord, groups, tail)
            : run_mode<u64>(c, O, coord, groups, tail));
    all_complete &= ok;
    selected.push_back(c.name);
  };
  // Fast full search: all positive odd n are one CRT run modulo 2.
  // The old three-class split (1 mod 8, 3 mod 4, 5 mod 8) repeats the
  // expensive A/B wheel generation and radix sorting three times.
  if (O.mode == "odd" || O.mode == "all") {
    Config c("odd", 2, 1, A, B, true);
    run(c);
  }
  if (g_stop) {
    std::cerr << "Interrupted. Re-run the same command to resume.\n";
    return 130;
  }
  // Legacy single-class modes remain available for cross-checks/resume.
  if (O.mode == "1mod8") {
    Config c("1mod8", 8, 1, A, B, true);
    run(c);
  }
  if (g_stop) {
    std::cerr << "Interrupted. Re-run the same command to resume.\n";
    return 130;
  }
  if (O.mode == "3mod4") {
    Config c("3mod4", 4, 3, A, B, false);
    run(c);
  }
  if (g_stop) {
    std::cerr << "Interrupted. Re-run the same command to resume.\n";
    return 130;
  }
  if (O.mode == "5mod8") {
    Config c("5mod8", 8, 5, A, B, false);
    run(c);
  }
  if (g_stop) {
    std::cerr << "Interrupted. Re-run the same command to resume.\n";
    return 130;
  }

  // A partial --chunk-begin/--chunk-end run intentionally does not claim global
  // completion.
  bool full_range = !O.self_test && (O.begin == 0 && O.end == ~u64(0));
  if (all_complete && full_range)
    std::cerr << "SEARCH COMPLETE: reduce chunk minima to global records.\n";
  else if (!O.no_merge)
    std::cerr << "[merge] skipped: search range is incomplete; use same "
                 "work-dir to resume.\n";
  return 0;
}

int main(int ac, char **av) {
  try { return search_main(ac, av); }
  catch (const std::exception &e) {
    std::cerr << "error: " << e.what() << '\n';
    return 1;
  }
}
