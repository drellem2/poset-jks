#!/usr/bin/env python3
"""OEIS and LMFDB lookups for notes/moonshine_scoping.md.  Needs network access.

Every series computed by moonshine_scoping.py is sent to the OEIS search (JSON
interface) by its first terms; the first hits are printed with their A-numbers
and names.  The holomorphic eta products eta_g of S_5 on Lie_5 are compared,
coefficient by coefficient, with the LMFDB newforms of the same level and
weight (traces of a_n, n <= 100).  Results are informational: nothing here is
asserted, and the exit status is 0 unless the network fails.

Run from compute/:  python3 moonshine_lookup.py > output/moonshine_lookup.txt
"""

import json
import subprocess
import sys
import time
import urllib.parse
import urllib.request

import moonshine_scoping as ms
from poset_jks_check import automorphisms, cycle_type, sign, transitive_closure
from poset_lie_structure import closed_formula


def fetch(url):
    """JSON from url.  The LMFDB answers urllib with a captcha page, so curl
    is used when it is available."""
    try:
        out = subprocess.run(["curl", "-s", "-m", "30", "-A", "poset-moonshine-scoping/1.0", url],
                             capture_output=True, check=True).stdout
        return json.loads(out.decode())
    except (OSError, subprocess.CalledProcessError, ValueError):
        pass
    req = urllib.request.Request(url, headers={"User-Agent": "poset-moonshine-scoping/1.0"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode())


def oeis(terms, nhits=3):
    q = ",".join(str(x) for x in terms)
    data = fetch("https://oeis.org/search?" + urllib.parse.urlencode({"q": q, "fmt": "json"}))
    time.sleep(1.0)
    if not data:
        return []
    return [(f"A{d['number']:06d}", d["name"]) for d in data[:nhits]]


def report(label, series, skip=0, nterms=16):
    terms = series[skip:skip + nterms]
    hits = oeis(terms)
    print(f"{label}\n  terms: {', '.join(map(str, terms))}")
    if not hits:
        print("  OEIS: no match")
    for a, name in hits:
        print(f"  OEIS: {a}  {name[:110]}")


def main():
    N = ms.NTERMS + 1
    print("== candidate 1 ==")
    b, c, cm = ms.witt_layer_numbers(ms.A006455)
    report("b_n = n [x^n] log A (n >= 1)", b[1:], nterms=12)
    report("c_n = dim V_n^(S_n) (n >= 1)", c[1:], nterms=12)
    report("c^-_n (sign-isotypic) (n >= 1)", cm[1:], nterms=12)
    report("c_n + c^-_n = dim V_n^(A_n) (n >= 1)", [x + y for x, y in zip(c[1:], cm[1:])], nterms=12)

    print("== candidate 2 ==")
    for name, (rel, n), _ in ms.PP_EXAMPLES:
        rel = transitive_closure(rel, n)
        seen = set()
        for g in sorted(automorphisms(rel, n)):
            if sign(g) != 1 or cycle_type(g) in seen:
                continue
            seen.add(cycle_type(g))
            T, _, _ = ms.quotient_formula(rel, n, g, N)
            if all(x <= 1 for x in T[:12]):
                continue
            report(f"{name}, g of type {cycle_type(g)}", T, nterms=20)

    print("== candidate 3 ==")
    for m in (2, 3):
        report(f"chain_{m} x N", ms.euler_product({k: -min(k, m) for k in range(1, N)}, N), nterms=20)
    exps = {}
    for i in range(1, N):
        if 2 * i - 1 < N:
            exps[2 * i - 1] = exps.get(2 * i - 1, 0) - 1
        for j in range(i + 1, N):
            if 2 * (i + j - 1) < N:
                exps[2 * (i + j - 1)] = exps.get(2 * (i + j - 1), 0) - 1
    report("N x N, transpose", ms.euler_product(exps, N), nterms=20)

    print("== candidate 4: Lie_5 ==")
    rel, n = ms.antichain(5)
    shapes = {}
    for g in automorphisms(rel, n):
        ct = cycle_type(g)
        if ct not in shapes:
            o = ms.order(g)
            shapes[ct] = ms.frame_shape({e: closed_formula(rel, n, ms.power(g, e))
                                         for e in range(1, o + 1)}, o)
    for ct, r in sorted(shapes.items()):
        # eta(t tau)^(24/t) is supported on q^(1 + t k): OEIS omits the zeros,
        # so the lookup uses the progression
        step = min(r) if len(r) == 1 else 1
        f = ms.eta_quotient(r, 4 * N)[::step]
        report(f"eta_g, g of type {ct}, Frame shape {ms.fmt_r(r)} (coefficients of "
               f"q^(1 + {step}k), k = 0, 1, ...)", f, nterms=16)
        T = ms.eta_quotient({t: -x for t, x in r.items()}, 4 * N)[::step]
        report(f"Fock trace q^-1 T_g = 1/eta_g, type {ct} (coefficients of q^({step}k))",
               T, nterms=16)
    lmfdb = {(1, 12): "1.12.a.a", (2, 6): "4.6.a.a", (3, 4): "9.4.a.a",
             (4, 3): "16.3.c.a", (6, 2): "36.2.a.a"}
    for (t, k), label in lmfdb.items():
        url = "https://www.lmfdb.org/api/mf_newforms/?" + urllib.parse.urlencode(
            {"label": label, "_format": "json", "_fields": "label,traces,dim"})
        d = None
        for attempt in range(3):
            try:
                d = fetch(url)
                break
            except ValueError:  # rate limiting returns an HTML page
                time.sleep(30.0)
        if d is None:
            print(f"LMFDB {label}: no JSON answer (rate limited?); not compared")
            continue
        rec = d["data"][0]
        tr = rec["traces"][:99]               # a_1, ..., a_99
        f = ms.eta_quotient({t: 24 // t}, 99)  # coefficients of q^1, ..., q^99
        same = (rec["dim"] == 1 and tr == f)
        print(f"LMFDB {label} (dim {rec['dim']}): a_n for n < 100 "
              f"{'EQUAL' if same else 'DIFFER'} to eta({t}tau)^{24 // t}; "
              f"Sturm bound for weight {k}, Gamma0({t * t}): {ms.sturm_bound(k, t * t)}")
        time.sleep(1.0)
    return 0


if __name__ == "__main__":
    sys.exit(main())
