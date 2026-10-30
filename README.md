# poset-jks

Research program on a poset generalization of the Joyal–Klyachko–Stanley theorem.

**Conjecture.** For a finite poset P on [n], the top homology of the lattice of
order-preserving partitions of P is, as an Aut(P)-module, the sign twist of the
span of {w·e_ζ : w a linear extension of P} in C[S_n], where e_ζ is the
cyclic Fourier idempotent. For the antichain this is classical JKS; the
dimensions agree for every P by Jenča–Sarkoci. Checked by computer for all
posets with n ≤ 5.

The note: [`notes/poset_jks_research_note.tex`](notes/poset_jks_research_note.tex).
Open problems are in its sections "Status: proved, supported, and open" and
"Concrete next research steps".

`./build.sh` builds the note to PDF if a TeX toolchain is present.
