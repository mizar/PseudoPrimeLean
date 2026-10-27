// Exact boundary regressions for the full unsigned 128-bit domain.
#define main search_program_main
#include "search.cpp"
#undef main

int main() {
  u128 n = ((u128)1 << 64) + 1;
  assert(to_string_u128(n) == "18446744073709551617");
  u128 root = ((u128)1 << 40) - 1;
  assert(is_square_u128(root * root));
  assert(!is_square_u128(root * root - 2));
  assert(!is_square_u128(((u128)1 << 80) - 1));
  assert(is_square_u128((u128)1 << 80));
  assert(parse_u128("340282366920938463463374607431768211455") == U128_MAX);
  for (std::string text : {TWO128, TWO128 + "0", std::string(""), std::string("-1")}) {
    bool rejected = false;
    try { (void)parse_u128(text); } catch (const std::runtime_error &) { rejected = true; }
    assert(rejected);
  }
  for (u64 r : std::vector<u64>{0, 1, 2, (u64(1)<<32)-1, (u64(1)<<63), UMAX-1, UMAX}) {
    u128 sq = (u128)r*r;
    assert(is_square_u128(sq));
    if (r > 1) assert(!is_square_u128(sq-1));
    if (r) assert(!is_square_u128(sq+1));
  }
  assert(!is_square_u128(U128_MAX));
  assert(!is_square_u128(U128_MAX-1));
  u64 random = 0x9e3779b97f4a7c15ULL;
  auto next = [&]() { random ^= random << 13; random ^= random >> 7; random ^= random << 17; return random; };
  for (u64 m : std::vector<u64>{1, 3, 5, 583573, 1009091, UINT32_MAX}) {
    FastMod fm(m);
    for (int i=0;i<10000;++i) {
      u128 x=((u128)next()<<64)|next();
      assert(fm.mod128(x)==x%m);
    }
    assert(fm.mod128(U128_MAX)==U128_MAX%m);
  }
  for (bool kind : {false, true}) {
    NON_ONE = kind;
    THRESHOLD = 3;
    std::vector<FirstFailGroup> tail;
    tail.emplace_back(std::vector<int>{3, 5});
    tail.emplace_back(std::vector<int>{7, 11});
    for (u128 x : std::vector<u128>{3, 15, 91, n, ((u128)1 << 80) - 1,
                                  ((u128)1<<127)+123, U128_MAX}) {
      int expected = 3;
      while (NON_ONE ? legendre128(x, expected) == 1 : legendre128(x, expected) != -1)
        expected = next_odd_prime(expected);
      assert(first_bad(x, tail).first == expected);
    }
    THRESHOLD = 17;
    assert(allow_m(3, 0) == !kind);
    assert(allow_m(3, 1));
    assert(!allow_m(3, -1));
    for (std::vector<int> ps : {std::vector<int>{3,5,7},std::vector<int>{3,5,7,11,13,17}}) {
      Wheel wheel(1,0,ps,std::vector<int>(ps.size(),1),std::vector<int>(ps.size(),1));
      for (u128 lo : std::vector<u128>{((u128)1<<64)+7,((u128)1<<127)+11,U128_MAX-1000}) {
        std::vector<u128> got, expected;
        wheel.generate(lo,lo+500,got);
        RadixScratch<u128> scratch;
        scratch.sort(got,lo,lo+499);
        for (u128 x=lo;x<lo+500;++x) {
          bool pass=true;
          for(int p:ps) if(!allow_m(p,legendre128(x,p))) pass=false;
          if(pass) expected.push_back(x);
        }
        assert(got==expected);
      }
    }
    THRESHOLD=131;
    CoordGroup group({79,83,89},15,14);
    for (u128 tp : std::vector<u128>{((u128)1<<80)+31,((u128)1<<120)+17,(U128_MAX-1000)/14})
      for (u64 tn : {0ULL,3ULL,17ULL}) {
        u128 x=tp*14-(u128)tn*15;
        bool pass=true;
        for(int p:group.ps) if(!allow_m(p,legendre128(x,p))) pass=false;
        assert(group.pass(group.akey(tp),group.bkey(tn))==pass);
      }
  }
  std::map<int, std::pair<u128, u64>> minima;
  minima.try_emplace(3, std::pair<u128,u64>{n, 1});
  assert(to_string_u128(minima.at(3).first) == "18446744073709551617");
  std::cout << "Full 128-bit parsing, squares, 60000 modular reductions, wheels and both witness kernels passed\n";
}
