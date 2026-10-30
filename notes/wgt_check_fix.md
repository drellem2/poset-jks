# Fix of the `[wgt]` check in `compute/natural_isomorphism.py`

Source of the defect: `notes/audit_natural_isomorphism.md` §5. Fix commit: 7c10288.

## What was wrong

- `weighted_rank` built s_λ(C) from `pj.cyclic_classes(lin)`, the least rotation of each class.
- That word need not lie in Lin P. When it does not, the sum it builds is not s_λ(C).
- So the λ ≡ 1 control printed 5/6, 16/19, 63/80 (n = 4, 5, 6), and the "independent" counts did
  not test Theorem Ψ on those posets.

## What changed

- New `lin_class_reps(lin)`: for each cyclic class C, the least word of C ∩ Lin P.
  `weighted_rank` and `check_weights` use it (with a `reps_fn` hook for the control test).
- `check_weights` now fails unless λ ≡ 1 drops for **every** disconnected P. That drop is PROVEN
  (audit §5: Σ_C s_1(C) = Σ_{w∈Lin P} w ∈ Sh_n). So a return of the defect fails the script.
- No mathematics changed. The other checks' output is byte-identical.

## Results

- COMPUTED (`[wgt]`, n = 2..6): random admissible λ, independent 4/4, 10/10, 32/32, 126/126,
  636/636; λ ≡ 1 drops for 1/1, 2/2, 6/6, 19/19, 80/80 disconnected P. These agree with the
  audit's `psi_rank` counts.
- COMPUTED (positive control, `test_wgt_control_least_rotation_reps_fail`): `check_weights` with
  the old representatives prints 5/6 at n = 4 and returns False. The missed poset drops with the
  new representatives.
- COMPUTED: the audit's §5 diagnostic, with `pj.cyclic_classes` replaced by
  `N.lin_class_reps`, prints `0 0` (it printed `17 17` before the fix).

## Reproduce

Run from `compute/`:

    python3 natural_isomorphism.py --nmax 6 > output/natural_isomorphism.txt   # ~6 s, exit 0
    python3 -m unittest test_natural_isomorphism
    python3 -c "
    import natural_isomorphism as N, poset_jks_check as pj, audit_natural_isomorphism as A
    ps=A.enumerate_posets(6); p=N.P1; bad=mis=0
    for r in ps[6]:
      if len(A.components(r,6))<2: continue
      lin=set(pj.linear_extensions(r,6))
      rk,e=N.weighted_rank(r,6,[1]*6,p)
      if rk==e: bad+=1; mis+=any(x not in lin for x in N.lin_class_reps(lin))
    print(bad, mis)"          # prints: 0 0
