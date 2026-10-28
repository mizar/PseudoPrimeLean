#!/usr/bin/env python3
"""Check Lean declaration namespaces against their source directories.

Run from any directory. Hidden directories and archive are excluded. The JSON policy
lists established structural directories that share their parent public API namespace.
It permits only the listed base and named internal namespaces, not sibling API areas.
"""
from pathlib import Path
import argparse
import json
import re

def mask(text):
    """Blank nested comments and strings, retaining offsets and line numbers."""
    output = list(text)
    position = 0
    while position < len(text):
        end = position
        if text.startswith("/-", position):
            depth = 1
            end += 2
            while end < len(text) and depth:
                if text.startswith("/-", end):
                    depth += 1
                    end += 2
                elif text.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
        elif text.startswith("--", position):
            end = text.find("\n", position)
            if end < 0:
                end = len(text)
        elif text[position] == "'" and (position == 0 or
                not (text[position - 1].isalnum() or text[position - 1] in "_'")):
            literal = re.match(r"'(?:\\.|[^'\\\n])'", text[position:])
            if literal is None:
                position += 1
                continue
            end = position + len(literal[0])
        elif text[position] == '"':
            end += 1
            while end < len(text):
                if text[end] == "\\":
                    end += 2
                    continue
                if text[end] == '"':
                    end += 1
                    break
                end += 1
            end = min(end, len(text))
        else:
            position += 1
            continue
        for index in range(position, end):
            if text[index] != "\n":
                output[index] = " "
        position = end
    return "".join(output)


def inspect(path, root, policy):
    text = path.read_text(encoding="utf-8-sig")
    masked = mask(text)
    expected = ".".join(path.parent.relative_to(root).parts)
    directory = path.parent.relative_to(root).as_posix()
    exception = policy.get(directory)
    scopes = []
    errors = []
    count = 0
    pattern = re.compile(
        r"^(?:@\[[^\n]*\]\s*)?"
        r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
        r"(namespace|section|end|theorem|lemma|def|abbrev|structure|class|inductive|opaque|instance)"
        r"\b([^\n]*)", re.M)
    for match in pattern.finditer(masked):
        command, rest = match[1], match[2].strip()
        if command in ("namespace", "section"):
            scopes.append((command, rest.split()[0] if rest else ""))
            continue
        if command == "end":
            if scopes:
                scopes.pop()
            continue
        namespace = ".".join(name for kind, name in scopes if kind == "namespace")
        name = rest.split()[0] if rest else ""
        # Executable entry points deliberately live at the module root.
        if not namespace and name == "main":
            continue
        count += 1
        normal = namespace == expected or namespace.startswith(expected + ".")
        structural = exception and namespace in exception["namespaces"]
        if not (normal or structural):
            errors.append({"file": path.relative_to(root).as_posix(),
                           "line": masked.count("\n", 0, match.start()) + 1,
                           "namespace": namespace, "expected": expected,
                           "declaration": name})
    return count, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    policy = json.loads((Path(__file__).with_name("namespace_layout_policy.json"))
                        .read_text(encoding="utf-8"))["structural_directories"]
    files = sorted(path for path in (root / "PseudoPrime").rglob("*.lean")
                   if not any(part.startswith(".") or part == "archive"
                              for part in path.relative_to(root).parts))
    errors = []
    declarations = 0
    for path in files:
        count, items = inspect(path, root, policy)
        declarations += count
        errors.extend(items)
    report = {"files": len(files), "declarations": declarations,
              "structural_directories": len(policy), "violations": errors}
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for item in errors:
            print("{file}:{line}: {namespace} (expected {expected}) [{declaration}]".format(**item))
        print(f"Checked {len(files)} Lean files, {declarations} declarations; "
              f"{len(errors)} namespace violations.")
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
