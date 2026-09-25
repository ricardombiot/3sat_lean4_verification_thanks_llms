#!/usr/bin/env python3
"""Hila `forb` por las llamadas a la API del UP de `GPathM` en un módulo migrado.

En `lean/improves_bin` el UP recibe las ventanas prohibidas `forb`. Cada función de la API
lleva `forb` en una posición fija (tras sus N primeros argumentos). Este script:

  1. inserta `forb` en esa posición en cada llamada que tenga al menos N argumentos escritos y
     no lo lleve ya (los argumentos se leen con paréntesis/corchetes equilibrados);
  2. en cada `theorem`/`def`/`lemma` cuya cabecera acabe usando `forb` sin tenerlo como binder
     (ni como `variable`), añade `(forb : PathNodeId → Bool)` tras `(title : String)`, o tras
     `(d : NodeId)` si no hay título.

No toca pruebas que dividan `up` (el caso con revisión hay que darlo a mano). Los patrones de
`match`/`induction` (`| up g d title …`) no se tocan.

Uso:  scripts/thread_forb.py GraphPath/Model/Parents
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent

# nombre → nº de argumentos antes de `forb`
API = {
    "addNode": 3, "up": 3, "upFiltering": 4, "newRowIds": 2, "newRow": 3, "upMap": 2,
    "upSons": 2, "upOwners": 2, "gainedSons": 2, "gainedOwners": 2, "skipsWindow": 2,
    "addNode_nodes": 3, "addNode_gowners": 3, "addNode_current": 3, "addNode_map_parent": 3,
    "upMap_id": 2, "upMap_parents": 2, "upMap_sons": 2, "upMap_owners": 2,
    "mapId_of_mem_newRowIds": 2, "mem_newRow_iff": 3, "newRow_step": 3,
    "exists_shift_of_mem_newRowIds": 2, "parent_id_ne_none_of_mem_newRowIds": 2,
    "nodup_newRowIds": 2, "gainedOwners_subset": 2, "gainedSons_subset": 2,
    "addNode_node?_old": 3, "addNode_node?_below": 3, "addNode_node?_new": 3,
    "addNode_node?_new_of": 3, "IsChain_of_addNode": 3, "PairwiseOwned_of_addNode": 3,
    "chain_top_mem_newRowIds": 3, "chain_top_mapId": 3, "pathOf_addNode": 3, "denot_addNode": 3,
    "MachineOk_addNode": 3, "ChainG_addNode": 3, "SupportedG_addNode": 3, "InhabitedG_addNode": 3,
    "ChainSound_addNode": 3, "mem_upMap_sons": 2, "GN_addNode": 3, "GN_up": 3,
    "GN_upFiltering": 4, "MachineOk_upFiltering": 4, "exists_rowParent": 2,
}
OPEN, CLOSE = "([{⟨", ")]}⟩"
IDENT = re.compile(r"[A-Za-z_À-ɏͰ-Ͽ₀-ₜ'!?₀-₉.][A-Za-z0-9_À-ɏͰ-Ͽ₀-ₜ'!?₀-₉.]*")


def read_arg(s: str, i: int):
    """Returns the end index of the argument starting at i (after spaces), or None."""
    j = i
    while j < len(s) and s[j] == " ":
        j += 1
    if j >= len(s) or s[j] == "\n":
        return None
    c = s[j]
    if c in OPEN:
        depth = 0
        k = j
        while k < len(s):
            if s[k] in OPEN:
                depth += 1
            elif s[k] in CLOSE:
                depth -= 1
                if depth == 0:
                    return j, k + 1
            k += 1
        return None
    m = IDENT.match(s, j)
    if m and m.group(0) not in ("with", "at", "then", "else", "fun", "by", "from", "=>", "forb"):
        return j, m.end()
    if c == "_":
        return j, j + 1
    return None


SUFFIX = [(r"[A-Za-z0-9]+_addNode", 3), (r"[A-Za-z0-9]+_upFiltering", 4), (r"[A-Za-z0-9]+_up", 3)]


def thread_calls(s: str) -> tuple[str, int]:
    n = 0
    # module-specific lemmas named after the UP (`PN_addNode`, `Shape_upFiltering`, …)
    for rx, k in SUFFIX:
        for name in set(re.findall(r"(?<![A-Za-z0-9_.])(%s)(?![A-Za-z0-9_'?!])" % rx, s)):
            API.setdefault(name, k)
    names = sorted(API, key=len, reverse=True)
    pat = re.compile(r"(?<![A-Za-z0-9_.'?!])(?:GPathM\.)?(%s)(?![A-Za-z0-9_'?!])" % "|".join(map(re.escape, names)))
    out = []
    pos = 0
    for m in pat.finditer(s):
        if m.start() < pos:
            continue
        name = m.group(1)
        # skip binders/patterns: `| up g d …`, `def up`, `theorem up`
        before = s[max(0, m.start() - 12):m.start()]
        if re.search(r"(\|\s*|def\s+|theorem\s+|lemma\s+)$", before):
            continue
        k = API[name]
        i = m.end()
        ok = True
        for _ in range(k):
            r = read_arg(s, i)
            if r is None:
                ok = False
                break
            i = r[1]
        if not ok:
            continue
        nxt = read_arg(s, i)
        if nxt is not None and s[nxt[0]:nxt[1]] == "forb":
            continue
        if nxt is None:
            rest = s[i:i + 6].lstrip(" ")
            if rest.startswith("forb"):
                continue
        out.append(s[pos:i] + " forb")
        pos = i
        n += 1
    out.append(s[pos:])
    return "".join(out), n


def add_binders(s: str) -> tuple[str, int]:
    vm = re.search(r"variable[^\n]*\(forb : PathNodeId → Bool\)", s)
    var_pos = vm.start() if vm else len(s) + 1  # only declarations after it see it
    n = 0
    decl = re.compile(r"(?m)^(private )?(theorem|lemma|def) [^\n]*")
    pieces = []
    pos = 0
    for m in decl.finditer(s):
        start = m.start()
        end = s.find(":=", start)
        if end == -1:
            continue
        header = s[start:end]
        # A UP lemma gets its own binder next to `title` even below `variable (forb …)`: the
        # variable would otherwise become its *first* argument, and every call written as
        # `X g d title forb` would be wrong. Statements about `Reachable` keep using the variable.
        uses_var = "Reachable reqOf forb" in header
        if "forb" in header and "(forb" not in header and (start < var_pos or not uses_var):
            new = header
            for anchor in ("(title : String)", "(d : NodeId)"):
                if anchor in new:
                    new = new.replace(anchor, anchor + " (forb : PathNodeId → Bool)", 1)
                    break
            if new != header:
                pieces.append(s[pos:start] + new)
                pos = end
                n += 1
    pieces.append(s[pos:])
    return "".join(pieces), n


REVIEW_SPLIT = re.compile(
    r"(?P<ind>[ \t]*)simp only \[GPathM\.up\]\n(?P=ind)split\n(?P=ind)· exact (?P<call>(?P<name>[A-Za-z0-9]+)_addNode [^\n]*(?:\n(?P=ind)    [^\n]*)*)\n(?P=ind)· exact ")


def review_branch(s: str, all_text: str) -> tuple[str, int]:
    """`up` now has a third branch, `review (addNode …)` when a window was skipped. Close it with
    `X_review` (or `X_of_pruned (pruned_review _)`) when that lemma exists; otherwise leave the
    proof alone so the compiler reports it."""
    n = 0

    def repl(m):
        nonlocal n
        ind, call, name = m.group("ind"), m.group("call"), m.group("name")
        call_i = call.replace("\n" + ind + "    ", "\n" + ind + "        ")
        if re.search(r"theorem %s_review\b" % re.escape(name), all_text):
            wrap = f"{name}_review _ ({call_i})"
        elif re.search(r"theorem %s_of_pruned\b" % re.escape(name), all_text):
            wrap = f"{name}_of_pruned (pruned_review _) ({call_i})"
        else:
            return m.group(0)
        n += 1
        return (f"{ind}simp only [GPathM.up]\n{ind}split\n{ind}· split\n"
                f"{ind}  · exact {wrap}\n{ind}  · exact {call_i}\n{ind}· exact ")

    return REVIEW_SPLIT.sub(repl, s), n


def main() -> int:
    path = HERE / "AbsSatBin" / (sys.argv[1] + ".lean")
    s = path.read_text()
    s, a = thread_calls(s)
    s, b = add_binders(s)
    all_text = "\n".join(p.read_text() for p in (HERE / "AbsSatBin").rglob("*.lean") if p != path) + s
    s, c = review_branch(s, all_text)
    path.write_text(s)
    print(f"thread_forb {sys.argv[1]}: {a} llamada(s), {b} binder(s), {c} rama(s) de revisión")
    return 0


if __name__ == "__main__":
    sys.exit(main())
