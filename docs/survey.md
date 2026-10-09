# Certified computation: a literature and prior-art survey

For Matthew Fairtlough, 2026-10-09. Written by a survey agent (Fable 5.1) at
the overseer's request. Research only: nothing was built, edited or
committed. Every reference in the bibliography was checked against a
publisher record, the CrossRef DOI registry, arXiv, or the official
documentation; the two that could not be checked are marked UNVERIFIED.

## Summary

1. The pattern used five times in locus (untrusted producer emits literal data;
   a Boolean checker proved sound adjudicates it in the kernel) has two textbook
   names: it is a *certifying algorithm* with a *verified checker* (McConnell et
   al. 2011; Alkassar et al. 2014), and the kernel step is *proof by reflection*
   (Boutin 1997; Barendregt and Barendsen 2002).
2. The standing rule "if a kernel check takes minutes, the certificate is
   missing information; add a witness" is the same move the SAT community made
   from DRAT to LRAT: put hints in the certificate so the checker never searches.
3. The refinement theorem that carries the fast checker to the library meaning
   is what Isabelle's code generator calls a *code equation* and what Lean's
   `@[csimp]` attribute does for compiled code: a proved equation between the
   slow definition and the fast one.
4. "Erase the termination argument at run time" is automatic in Rocq extraction
   (Prop and accessibility proofs are erased; well-founded recursion combinators
   are inlined). Lean has no extraction; the equivalent is to keep fuel and
   bounds out of the *statement* and the *run-time path*, which is exactly the
   correction Matthew made in lax-logic on 2026-07-19 and 2026-08-26.
5. The one thing our practice does that the certifying-algorithm literature does
   not require is proving the producer *complete* (the matcher misses nothing);
   it is needed because a bisimulation certificate must list every move.
6. Gaps against the prior art: no independent re-check of the kernel (lean4checker
   or Lean4Lean); no measured profile of what the kernel spends time on; no
   streaming or incremental checking for large certificates; no written
   certificate-format specification separate from the Lean data type.
7. Nothing in the pattern is novel; what is specific to us is the axiom policy
   (kernel `decide` only, no compiler trust) and the generic evaluator reused
   across five checkers.

## Bibliography (verified)

Verification method is noted per entry: CR = CrossRef record for the DOI;
WS = publisher or index page fetched; AX = arXiv abstract page; DOC = official
documentation page fetched; SRC = source file fetched from the Lean repository.

Certifying algorithms and verified checkers
- [1] R. M. McConnell, K. Mehlhorn, S. Näher, P. Schweitzer. Certifying
  algorithms. Computer Science Review 5(2):119–161, 2011.
  doi:10.1016/j.cosrev.2010.09.009 (CR)
- [2] E. Alkassar, S. Böhme, K. Mehlhorn, C. Rizkallah. A framework for the
  verification of certifying computations. Journal of Automated Reasoning
  52:241–273, 2014. doi:10.1007/s10817-013-9289-2 (CR)
- [3] M. Abdulaziz, K. Mehlhorn, T. Nipkow. Trustworthy graph algorithms
  (invited talk). MFCS 2019. doi:10.4230/LIPIcs.MFCS.2019.1 (WS)

Trusted kernels and reflection
- [4] M. J. Gordon, A. J. Milner, C. P. Wadsworth. Edinburgh LCF. LNCS 78,
  Springer, 1979. doi:10.1007/3-540-09724-4 (CR)
- [5] S. Boutin. Using reflection to build efficient and certified decision
  procedures. TACS 1997, LNCS 1281, pp. 515–529. doi:10.1007/BFb0014565 (CR)
- [6] H. Barendregt, E. Barendsen. Autarkic computations in formal proofs.
  Journal of Automated Reasoning 28:321–336, 2002.
  doi:10.1023/A:1015761529444 (CR)
- [7] G. Gonthier, A. Mahboubi, E. Tassi. A small scale reflection extension
  for the Coq system. INRIA research report RR-6455, 2008.
  https://inria.hal.science/inria-00258384 (index record via Semantic
  Scholar; the HAL page itself refused automated access)
- [8] B. Grégoire, X. Leroy. A compiled implementation of strong reduction.
  ICFP 2002, pp. 235–246. doi:10.1145/581478.581501 (CR)
- [9] G. Gonthier. Formal proof: the four-color theorem. Notices of the AMS
  55(11), 2008. https://www.ams.org/notices/200811/tx081101382p.pdf
  UNVERIFIED (publisher returned 403; index rate-limited). Cited only as the
  standard large example of proof by reflection.

Translation validation and proof-carrying code
- [10] A. Pnueli, M. Siegel, E. Singerman. Translation validation. TACAS 1998,
  LNCS 1384, pp. 151–166. doi:10.1007/BFb0054170 (CR)
- [11] G. C. Necula. Translation validation for an optimizing compiler.
  PLDI 2000, pp. 83–94. doi:10.1145/349299.349314 (CR)
- [12] G. C. Necula. Proof-carrying code. POPL 1997, pp. 106–119.
  doi:10.1145/263699.263712 (CR)

SAT certificates and verified checkers
- [13] N. Wetzler, M. J. H. Heule, W. A. Hunt Jr. DRAT-trim: efficient checking
  and trimming using expressive clausal proofs. SAT 2014, pp. 422–429.
  doi:10.1007/978-3-319-09284-3_31 (CR)
- [14] L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann,
  P. Schneider-Kamp. Efficient certified RAT verification. CADE 2017,
  pp. 220–236. doi:10.1007/978-3-319-63046-5_14 (CR)
- [15] P. Lammich. Efficient verified (UN)SAT certificate checking. CADE 2017,
  pp. 237–254, doi:10.1007/978-3-319-63046-5_15; journal version, Journal of
  Automated Reasoning 64:513–532, doi:10.1007/s10817-019-09525-z (CR both)
- [16] Y. K. Tan, M. J. H. Heule, M. O. Myreen. cake_lpr: verified propagation
  redundancy checking in CakeML. TACAS 2021, pp. 223–241,
  doi:10.1007/978-3-030-72013-1_12; journal version, STTT 25:167–184, 2023,
  doi:10.1007/s10009-022-00690-y (CR both)

Certified model checking and bisimulation certificates
- [17] K. S. Namjoshi. Certifying model checkers. CAV 2001, pp. 2–13.
  doi:10.1007/3-540-44585-4_2 (CR)
- [18] J. Esparza, P. Lammich, R. Neumann, T. Nipkow, A. Schimpf, J.-G. Smaus.
  A fully verified executable LTL model checker. CAV 2013, pp. 463–478.
  doi:10.1007/978-3-642-39799-8_31 (CR)
- [19] S. Wimmer, J. von Mutius. Verified certification of reachability
  checking for timed automata. TACAS 2020, pp. 425–443.
  doi:10.1007/978-3-030-45190-5_24 (CR)
- [20] Q. Heath, D. Miller. A framework for proof certificates in finite state
  exploration. arXiv:1507.08716, 2015. https://arxiv.org/abs/1507.08716 (AX)
- [21] P. Lammich. Automatic data refinement. ITP 2013, pp. 84–99.
  doi:10.1007/978-3-642-39634-2_9 (CR)

Lean 4
- [22] H. Böving, S. Bhat, L. Cicolini, A. Keizer, L. Frenot, A. Mohamed,
  L. Stefanesco, H. Khan, J. Clune, C. Barrett, T. Grosser. Interactive
  bitvector reasoning using verified bit-blasting. Proc. ACM Program. Lang. 9
  (OOPSLA 2025), pp. 3259–3285. doi:10.1145/3763167 (CR)
- [23] Lean 4.12.0 release notes (bv_decide, LRAT, Lean.ofReduceBool).
  https://lean-lang.org/doc/reference/latest/releases/v4.12.0/ (DOC)
- [24] Lean language reference, "Validating a Lean proof".
  https://lean-lang.org/doc/reference/latest/ValidatingProofs/ (DOC)
- [25] Lean language reference, "Recursive definitions" (structural,
  well-founded, partial). https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/ (DOC)
- [26] Lean language reference, "Natural numbers" (kernel and compiler
  arbitrary-precision support). https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/ (DOC)
- [27] Lean source, `src/Init/Tactics.lean`, docstrings of `decide` and
  `native_decide`. https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean (SRC)
- [28] Lean source, `src/Lean/Compiler/CSimpAttr.lean`, docstring of `@[csimp]`.
  https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/CSimpAttr.lean (SRC)
- [29] Lean API docs, `implemented_by` attribute.
  https://leanprover-community.github.io/mathlib4_docs/Lean/Compiler/ImplementedByAttr.html (DOC)
- [30] Mathlib docs, `Mathlib.Tactic.NormNum.Core`.
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Core.html (DOC)
- [31] Mathlib docs, `Mathlib.Tactic.Polyrith`.
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html (DOC)
- [32] N. Voss. lean-pitfalls (community notes on `decide`, `native_decide`,
  `Lean.ofReduceBool`). https://github.com/nielsvoss/lean-pitfalls (WS)
- [33] S. Szeider. PBLean: pseudo-Boolean proof certificates for Lean 4.
  arXiv:2602.08692, 2026. https://arxiv.org/abs/2602.08692 (AX)
- [34] S. Szeider. Streaming LRAT certificates into Lean theorems
  (lrat-catcher). arXiv:2607.00815, 2026. https://arxiv.org/abs/2607.00815 (AX)
- [35] M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean.
  arXiv:2403.14064. https://arxiv.org/abs/2403.14064 (AX)

Rocq/Coq extraction, erasure and verified compilation
- [36] P. Letouzey. A new extraction for Coq. TYPES 2002, LNCS 2646,
  pp. 200–219 (published 2003). doi:10.1007/3-540-39185-1_12 (CR)
- [37] P. Letouzey. Extraction in Coq: an overview. CiE 2008, pp. 359–369.
  doi:10.1007/978-3-540-69407-6_39 (CR)
- [38] Rocq reference manual, chapter "Program extraction" (J.-C. Filliâtre,
  P. Letouzey). https://rocq-prover.org/doc/master/refman/addendum/extraction.html (DOC)
- [39] A. Bove, V. Capretta. Modelling general recursion in type theory.
  Mathematical Structures in Computer Science 15(4):671–708, 2005.
  doi:10.1017/S0960129505004822 (CR)
- [40] A. Anand, A. W. Appel, G. Morrisett, Z. Paraskevopoulou, R. Pollack,
  O. Savary Belanger, M. Sozeau, M. Weaver. CertiCoq: a verified compiler for
  Coq. CoqPL 2017. https://popl17.sigplan.org/details/main/9/CertiCoq-A-verified-compiler-for-Coq (WS)
- [41] M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter.
  Coq Coq correct! Verification of type checking and erasure for Coq, in Coq.
  Proc. ACM Program. Lang. 4 (POPL 2020). doi:10.1145/3371076 (CR)
- [42] Y. Forster, M. Sozeau, N. Tabareau. Verified extraction from Coq to
  OCaml. Proc. ACM Program. Lang. 8 (PLDI 2024), pp. 52–75.
  doi:10.1145/3656379 (CR)
- [43] E. H. Nielsen, S. Dima, L. Escot, O. Melkonian, H. Segoufin-Cholet,
  J. Chapman, Y. Forster, M. Sozeau, B. Spitters. Peregrine: a middle-end for
  code generation from proof assistants. TYPES 2026.
  https://www.iog.io/papers/peregrine-a-middle-end-for-code-generation-from-proof-assistants (WS)
- [44] S. Dima. Compiling Lean programs with Rocq's extraction pipeline. MPRI
  internship report, 2025-10-01, advised by Y. Forster.
  https://www.normalesup.org/~sdima/2025_extraction_report.pdf (PDF fetched)

Isabelle and HOL4/CakeML
- [45] F. Haftmann (with L. Bulwahn, T. Nipkow). Code generation from
  Isabelle/HOL theories. Isabelle system documentation, edition dated
  2026-01-18. https://isabelle.in.tum.de/doc/codegen.pdf (PDF fetched)
- [46] F. Haftmann, T. Nipkow. Code generation via higher-order rewrite
  systems. FLOPS 2010, LNCS 6009, pp. 103–117.
  doi:10.1007/978-3-642-12251-4_9 (CR)
- [47] M. O. Myreen, S. Owens. Proof-producing synthesis of ML from
  higher-order logic. ICFP 2012, pp. 115–126. doi:10.1145/2364527.2364545 (CR)
- [48] R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified
  implementation of ML. POPL 2014, pp. 179–191. doi:10.1145/2535838.2535841 (CR)

## Local evidence (read only)

### locus (`~/Lean/locus`, main)

- `docs/logic-checking-plan.md`. Records the failure (kernel `decide +kernel`
  on `checkC`, which made the kernel run the explorer, the canonicaliser and
  the matcher once per state per fixpoint round; `ssR.length = 12` alone did
  not finish in ten minutes) and fixes the route: compiled untrusted producer
  writes a Lean source file of literals (states, successor table, and for each
  matcher step the index of the state it renumbers to together with the
  renumbering witness, so the kernel checks one equation instead of searching
  for the renumbering); trusted Boolean checker `certCheck` proved sound; the
  fixpoint evaluator runs on Booleans over the successor table; the efficient
  checker is a refinement theorem, `certCheck cert = true` implies
  `checkG cert φ i = checkC S rules atoms ss φ i`. Standing rules: never ask
  the kernel to search; certificates are generated, never hand-written, and
  committed with the script; `native_decide` is excluded because it adds
  `Lean.ofReduceBool` outside the `[propext, Quot.sound]` pin; "if a kernel
  check takes more than a few minutes, the certificate is missing information;
  add a witness rather than waiting"; statements first.
- `docs/case-study/review-logic.md` §1. The pattern reused five times (closed
  checker, M1′, witness and lasso certificates, strong and weak bisimulation
  certificates, ABP ≈ buffer at 112 and 160 states). One evaluator over a
  successor function meant each checker was a small refinement. Each
  certificate gate was seen rejecting a corrupted certificate at least once.
- `docs/case-study/review-mac.md` §1. The simulator's match search has no
  correctness proof; each proposed match is a certificate that a checker
  proved sound against the bigraph library accepts or refuses. The checker was
  built and proved before any search existed. The search was later rewritten
  to find every match without re-proving soundness; completeness of the new
  search (C-occ″) was proved separately by the logic lane.
- `Logic/CertBisim.lean`. The certificate for strong and weak bisimulation:
  states of both systems with renumbering witnesses, the tagged successor
  tables, a finite relation on state indices, and for weak bisimulation the
  answering path for every obligation, "so the kernel checks paths and never
  searches". The file notes that soundness needs the graphs to be exact: a
  library move of a related agent must appear in the graph, otherwise a
  certificate could pass by omitting the move the other side cannot answer.
  That is completeness of the matcher (G1), a hypothesis for both systems.
- `Logic/CertBisimProof.lean`. `step_tag_sound`, `step_tag_complete`,
  `edge_sound`, `edge_complete`, `walk_sound`, `answer_sound`, and the two
  headline theorems `certBisimSound` and `certWeakBisimSound` (both marked
  PROVED in the file).
- `Logic/Examples/ABPCert.lean`. Generated by `Logic/Examples/ABPGen.lean`
  from the untrusted producer `Logic/CertBisimProduce.lean`; the certificate
  is literal data; every verdict is `by decide +kernel` (lines 595–645).
- `docs/protocol.md` line 73: allow-list `[propext, Quot.sound]`, with named
  exceptions at `[propext, Quot.sound, Classical.choice]`.

### lax-logic-in-lean (paths as on `origin/main` at 9783484)

*Corrected 2026-10-09 after a check by the LaxLogic manager session: the
local checkout this survey first read was on branch `blueprint-dev-chapter`,
206 commits behind `origin/main`, before the syntax reorganisation. Paths
below are those on `origin/main`; line numbers are unchanged.*

The implementation that spent its time on termination bounds. Two episodes
are on record, both with measurements:

- `LaxLogic/PLL/G4/G4Dec.lean` ("Termination C: the decider", F&M Theorem 2.8).
  The backward search `search W as fuel V Γ C` (line 112) is made structural by
  a fuel parameter; the header says fuel `|seqEnumF \ V| + 1` always suffices
  because every call inserts the current sequent into the visited set and the
  gated sequents live in the finite space of `PLLG4Space.lean`. `decideFuel`
  (line 629) computes that fuel from the cardinality of the finite sequent
  space, and the `Decidable` instance `decidablePLL`
  (line 675, axioms `[propext, Quot.sound]`) runs the search at that fuel.
  `PROGRESS.md` §2 records the cost: "the exponential cost of `decide` lives
  ONLY in the `decideFuel` completeness packaging, never in the search itself.
  Measured: weight-6 goal 39 ms via `find` vs >90 s aborted via `decide`."
  (`find` in `LaxLogic/PLL/Search/Demos.lean` runs the same search at a hand
  fuel of 10,000.) `HANDOFF.md` line 726 notes the instance "is total but
  exponential; fuel is computed arithmetically, never the powerset". This is
  the case Matthew describes. **Where the cost actually is** (`docs/demos.md`
  §3, on `⊢ ◯p → ◯p`): `(enum {p} 5).card` alone takes 6.06 s, `decideFuel`
  5.83 s, and the search at that fuel 5.86 s. The 54-digit fuel number is
  free, and on this one *provable* sequent the search adds nothing
  measurable. There the whole cost is *constructing* the weight-bounded
  formula space `enum`, which `.card`
  materialises level by level (with |enum|² products and quadratic `Finset`
  deduplication). The arithmetic was cheap, but the set it counts still had to
  be built. With a hand fuel of 10,000 the same sequents take 34–72 ms.
  This measurement does not show that the search is cheap in general: the
  next entry records a second, separate cost.
- **Second cost: the fuelled engine itself.** `PROGRESS.md` §10 (2026-07-19, "fuel demoted"). After Matthew asked "are you
  using the most efficient versions?", the fuel-free `G4cTm.find` decided the
  whole oracle benchmark at 0 ms where the fueled `search` "ground for minutes"
  on refutable goals; "the unpredictable failing cost was an artifact of the
  fueled engine, not the problem"; "fuel appears nowhere in the decision
  path". `G4cTm` lives in `LaxLogic/PLL/G4/G4Term.lean`, `LaxLogic/PLL/Search/`
  and related files.
- `HANDOFF.md` §2026-08-26e. A first design re-ran the LJF◯ fueled search
  under kernel `decide` with per-cell minimal-fuel metering; it "was WORKING
  but wrong-shaped: Matthew asked why fuel was in the statement at all". It
  was replaced by the G4c certificate pattern already in the repository:
  `tools/RCellsGen.lean` runs the budgeted `G4cTm.findBounded` searcher
  compiled and untrusted (budget 4·10⁵ nodes), prints the found proof terms
  as Lean source, and the kernel only type-checks the literals: 442 cells in
  27 s. The fuel byproducts were kept as cross-checks in `tools/RCFuel.lean`.
  (`docs/next-session.md` lines 427–447 was written earlier the same day,
  while the fuelled design was running. Its statement that the fuelled gate
  is still in use is stale for table promotion. A separate use remains
  fuelled: the two-sided engine's proof side, `wip/ljfo_link.lean`,
  `laxND_of_searchProves (f := 16) (by decide)`, re-runs the focused search
  under fuel in the kernel. Confirmed by the LaxLogic manager, 2026-10-09.)
- Other certificate-style checking in the repository: `tools/Cert.lean`
  (`frjcert`: sequent in, a minimised countermodel written as a self-contained
  Lean file, Lean run on it, the verdict carrying Lean's exit code and
  `#print axioms` output); `RNDB/FRJCertEntries.lean` (banked entries
  `frjCertEntry … (by decide)`); `LJF/OFuel.lean` and siblings (a fuel-founded
  interpolant where "every fuel level is sound; sufficiency is only needed for
  minimality", i.e. fuel is used for soundness-by-construction and the bound
  matters only for a completeness statement). These fuel-founded definitions
  carry a second cost, at build time rather than run time: `LJF/OFuelPFam.lean`
  (17 mutual definitions by well-founded recursion) takes 3.0 s as an `unsafe
  def`, 510 s with the kernel check skipped, and 1,463 s as committed
  (`docs/ui-ljfo-clause-table.md` §4.20). So `WellFounded.fix` costs at
  elaboration even where it costs nothing at run time.

I did not re-run any of these; the timings are those recorded in the files.

## Q1. Certifying algorithms and checkers

Certifying algorithms (McConnell, Mehlhorn, Näher, Schweitzer [1]). A
certifying algorithm returns, with each output, a witness that the output is
correct, such that a simple checker can verify the output from the input and
the witness. The paper's thesis is that for complex algorithmic tasks only
certifying algorithms are satisfactory, and it argues the concept is universal
(every algorithm can be made certifying, at a cost). The checker should be
simple enough to be trusted or verified; the algorithm itself need not be. The
follow-up by Alkassar, Böhme, Mehlhorn and Rizkallah [2] closes the loop by
verifying the checker: the checker's C code is verified with VCC and its
mathematical correctness (witness implies property) in Isabelle/HOL. Abdulaziz,
Mehlhorn and Nipkow [3] carry this into verified graph algorithms. Mapping to
our pattern: it is this pattern exactly. The compiled producer is the
certifying algorithm, the literal Lean data is the witness, `certCheck` and
`wbisimCheck` are the checkers, and `certBisimSound` is the "witness implies
property" theorem that [2] proves in Isabelle. The one point where we go beyond
[1] is that we also prove the producer complete (C-occ″) because the
bisimulation certificate must list every move; see Q4.

LCF-style trusted kernels (Gordon, Milner, Wadsworth [4]). Theorems are values
of an abstract type that only the kernel's inference rules can construct; any
amount of untrusted search may run outside provided it ends by invoking kernel
rules. Lean is in this family: the elaborator and tactics are untrusted; the
kernel checks the term. Mapping: our axiom policy ("only `propext` and
`Quot.sound`") is a statement about what the kernel is allowed to assume, and
excluding `native_decide` keeps the compiler out of the trusted base. The
Lean reference's "Validating a Lean proof" page [24] states the trust boundary
plainly: native evaluation "can be used to create invalid proofs whenever the
native evaluation of a term disagrees with the kernel's evaluation", and every
`implemented_by`/`extern` replacement becomes part of the trusted base; it also
notes that external checkers (`lean4checker`, `comparator`) cannot check such
proofs, and that native tactics now use dedicated axioms rather than one
shared `Lean.trustCompiler`. (This survey first dated the change to Lean
4.35. lax-logic-in-lean observes the per-proof axioms already under Lean 4.31,
its toolchain since 2026-07-12; see `docs/ledger-campaign-2026-09-16.md` line
39. The version in which the change landed needs re-checking against the
reference.)

Proof by reflection (Boutin [5]; Barendregt and Barendsen [6]; SSReflect [7];
Grégoire and Leroy [8]). A decision procedure is written as a function inside
the logic, proved sound once (`check x = true → P x`), and then applied: the
proof of `P x` is the soundness lemma applied to a computation the kernel
performs by reduction. Boutin showed this beats the LCF-style approach for
ring equalities; Barendregt and Barendsen named the principle (the "Poincaré
principle": a computation step needs no recorded proof) and showed how
computations inside the proof checker keep proofs small. Grégoire and Leroy's
compiled strong reduction (`vm_compute`) made it fast in Coq. SSReflect's
"small-scale" variant uses Boolean predicates and decidability pervasively so
that reflection is used at every step, not only for large decision procedures.
Gonthier's four-colour proof [9, UNVERIFIED] is the standard large example.
Mapping: `theorem … : checkG cert φ 0 = true := by decide +kernel` is a
reflective proof; the kernel reduces the Boolean, and `certBisimSound` is the
soundness lemma. Our choice of kernel `decide` rather than compiled evaluation
puts us at the Boutin end (no trusted evaluator) rather than the `vm_compute`
or `native_decide` end.

Translation validation (Pnueli, Siegel, Singerman [10]; Necula [11]).
Instead of verifying a compiler, check each run: after each compilation,
prove that the output is equivalent to the input, using a simulation relation
the compiler's pass is instrumented to emit. Necula's proof-carrying code [12]
is the related idea for mobile code: the producer ships a proof, the consumer
checks it. Mapping: the "search proposes, checker decides" rule in review-mac is
translation validation applied to a matcher: the match is checked after each
run rather than the search being verified. The difference is that in our case
the checker's own correctness is a Lean theorem, whereas Pnueli's validator and
Necula's checker are trusted code. Translation validation is the right name for
the run-time half of our pattern; certifying algorithm with a verified checker
is the name for the whole.

SAT certificates: DRAT, LRAT, verified checkers [13]–[16]. DRAT-trim [13]
checks clausal proofs in which each step is a clause the checker must justify
by unit propagation, i.e. the checker searches. LRAT [14] adds hints (the
clause identifiers used by each propagation) so that checking is linear and
search-free, and the paper's checker is verified in ACL2 and faster than the
unverified DRAT-trim. Lammich's GRAT [15] takes the same route in Isabelle: an
unverified tool enriches the certificate so a verified checker can run in
linear time. cake_lpr [16] is the strongest form: the checker is verified down
to machine code via CakeML. Mapping: our rule "add a witness rather than
waiting" is the DRAT to LRAT move. The renumbering witnesses in the state
certificate and the answering paths in the weak-bisimulation certificate are
hints in the LRAT sense. The SAT community also shows the next step we have not
taken: a written format specification with more than one checker (DRAT-trim,
GRAT, cake_lpr, Lean's checker [22]) so that a certificate can be re-checked
independently.

Certified model checking and bisimulation certificates [17]–[21]. Namjoshi
[17] proposed that a model checker output a deductive proof (invariants and
ranking functions) checkable independently. Esparza et al. [18] took the other
road: a fully verified model checker in Isabelle, with executable code via the
code generator. Wimmer and von Mutius [19] combined the two: an unverified
model checker (with all its optimisations) emits a certificate (a reachable
set closed under successors), and a verified checker in Isabelle validates it;
this is the exact shape of M1′ (the producer explores; the certificate is the
set of states plus the successor table; the checker verifies closure). Heath
and Miller [20] define proof certificates for reachability, non-reachability,
bisimulation and non-bisimulation over labelled transition systems, checked by
a focused proof system whose soundness does not depend on the "clerk and
expert" programs that interpret the certificate; this is the closest published
analogue of `CertBisim.lean`. Lammich's data-refinement framework [21] is the
Isabelle machinery by which an abstract specification (a set, a relation) is
refined to an efficient data structure with a proved refinement theorem; it is
the general form of our "evaluator over the successor table equals evaluator
over the library semantics" theorem.

## Q2. Lean 4 precedents

`bv_decide` / LeanSAT [22], [23]. The goal is bit-blasted to a Boolean circuit,
an external SAT solver (CaDiCaL) refutes it and emits an LRAT proof, and a
checker with a soundness proof in Lean validates the LRAT proof; the proof of
the goal is then obtained "by reflection". The release notes [23] state the
trust: "proofs generated by this tactic use `Lean.ofReduceBool`, so this tactic
includes the Lean compiler as part of the trusted code base". The OOPSLA 2025
paper [22] describes the verified bit-blaster, a small trusted base, and "one
axiom indicating trust in the Lean compiler". So `bv_decide` is our pattern
with one parameter set differently: the checker is evaluated by compiled code
under an axiom, not by the kernel. Two 2026 follow-ups keep that setting: PBLean
[33] (pseudo-Boolean VeriPB certificates; "a Boolean checker function whose
soundness is fully proved in Lean and executed as compiled native code", chosen
because explicit proof terms exhausted memory at tens of thousands of steps)
and lrat-catcher [34] (LRAT certificates streamed into Lean while the solver
runs, with a resumable checker state). Under our axiom policy these are not
admissible as they stand; they are nevertheless the best-documented Lean
examples of checker design, streaming and memory behaviour.

`norm_num` [30] and `polyrith`/`linear_combination` [31]. `norm_num` builds
explicit proof terms (`IsNat`, `IsInt`, `IsRat` results) through a simp-based
driver with extensions; it does not rely on kernel reduction of a decision
procedure. `polyrith` was the external-oracle pattern: it called a Sage service
to find polynomial coefficients and emitted a `linear_combination` call, which
Lean then checks by `ring`; the Mathlib page now says the Sage service is shut
down and the tactic is unsupported, but the design (external search, Lean
check of a small certificate) is the one that matters here. Both are
certificate patterns at tactic scale: the certificate is a proof term or a list
of coefficients, not data checked by a Boolean function.

`decide` versus `native_decide` [27], [24], [32]. The `decide` docstring:
`decide +kernel` "uses the kernel for reduction instead of the elaborator",
"ignores transparency and can unfold everything", and "reduces the `Decidable`
instance only once instead of twice"; the warning that matters to us is
"`Decidable` instances defined by well-founded recursion might not work because
evaluating them requires reducing proofs. Reduction can also get stuck on
`Decidable` instances with `Eq.rec` terms." `decide +native` "uses the native
code compiler (`#eval`) to evaluate the `Decidable` instance, admitting the
result via an axiom", and `native_decide` "adds the entire Lean compiler to the
trusted part". The community pitfalls page [32] adds that Mathlib does not
accept `native_decide`, and gives a worked example where a wrong
`implemented_by` makes `decide` and `native_decide` prove contradictory
theorems. The reference manual [25] states the underlying fact: applications
of functions defined by well-founded recursion "are not necessarily
definitionally equal to their return values, but this equality can be proved
as a proposition", whereas structural recursion reduces definitionally; and
functions marked `partial` "are treated as opaque constants by the kernel and
are neither unfolded nor reduced". Consequences for our checkers: a checker
that must run under kernel `decide` has to be structurally recursive (or
fuelled with structural fuel over a literal), and its data must be of types the
kernel reduces well. The kernel does accelerate natural-number literals and
their basic operations with an arbitrary-precision library [26], so `Nat`
indices and comparisons are cheap in the kernel; lists and structures are not
accelerated.

`implemented_by`, `@[csimp]`, `partial def`, compiled versus kernel evaluation
[28], [29], [25]. `implemented_by` "instructs the compiler to use a different
function as the implementation"; "the kernel and type checking are
unaffected", except for tactics that call native code, and "the provided
implementation is not checked to be equivalent to the original definition.
This makes it possible to prove `False` with `native_decide` using incorrect
implementations." `@[csimp]` "tags compiler simplification theorems, which
allow one value to be replaced by another equal value in compiled code"; the
theorem must prove `@f = @g`, and the replacement happens "in compiled code,
but not in the type theory. In this sense, `@[csimp]` is a safer alternative to
`@[implemented_by]`." So Lean already has, built in, the two faithfulness
regimes of the extraction literature: an unproved realisation
(`implemented_by`, like Rocq's `Extract Constant`) and a proved one (`csimp`,
like an Isabelle code equation). Our refinement theorems are `csimp`-shaped
statements that we apply by hand in the proof rather than registering with the
compiler.

Extraction and verified code generation for Lean. I searched for "verified
compiler", "verified code generation" and "program extraction" for Lean 4. There
is no verified extraction or verified compiler for Lean 4. What exists: the
unverified self-hosted compiler to C; Lean4Lean [35], a typechecker for Lean
written in Lean (not a compiler); Peregrine [43], which adds a Lean front end
producing Rocq's erased intermediate language λ□, with MetaRocq's verified
erasure used for the Rocq front end and verification of the Lean front end
stated as a long-term hope; and Dima's MPRI report [44], which implemented
erasure from Lean to λ□ "adapting the erasure algorithm introduced by Letouzey
(2004) to Lean expressions" and measured the extracted executables at about 2.5
times slower than the Lean compiler's output. So "Lean has no extraction" is
correct today in the sense that matters: there is no supported, let alone
verified, route from a Lean definition to code other than Lean's own compiler.

## Q3. Rocq/Coq extraction, Isabelle, CakeML

Letouzey's extraction [36], [37], [38]. Extraction maps a Coq term to an ML
program by erasing everything in `Prop` and all types, keeping the
computational skeleton. The Rocq manual [38] states the division: programs
(in `Type`) have computational content; proofs (in `Prop`) "are devoid of
computational meaning and are therefore erased". Three things from the manual
bear directly on Matthew's principles. First, well-founded recursion
combinators "are still automatically inlined" even when auto-inlining is off,
so a function defined by well-founded recursion extracts to ordinary general
recursion with no trace of the measure or the accessibility proof. Second,
axioms must be realised by hand with `Extract Constant`, and "it is the
responsibility of the user to ensure that the ML terms given to realize the
axioms do have the expected types"; and "inconsistent logical axioms may lead
to incorrect or non-terminating extracted terms". Third, erasure can require
type-unsafe casts (`Obj.magic`) when dependent types are flattened. Letouzey
[36] proves correctness for a theoretical model of the extraction and [37]
surveys the mechanism, its limits and the pitfalls (efficiency of extracted
code, the cost of `Prop`-vs-`Type` discipline, axioms). The efficiency pitfall
most relevant to us: extracted code is only as efficient as the Coq definition
it came from; if the definition carries a counter, a bound or a check that is
in `Type`, the counter is kept.

Bove and Capretta [39]. A general-recursive function is defined by structural
recursion on an inductively defined *accessibility* (domain) predicate; the
proof that the domain predicate holds is a separate theorem. Since the
predicate is in `Prop`, extraction erases it, and the extracted function is
the original general-recursive one. This is the formal statement of "the
termination proof belongs to the theory, not to the run-time code". Lean's
well-founded recursion is the same construction internally (recursion over the
accessibility proof), which is why its applications do not reduce
definitionally in the kernel [25]: the kernel would have to reduce the
accessibility proof.

CertiCoq [40], MetaCoq/MetaRocq [41], verified extraction [42]. CertiCoq is a
compiler from Gallina to C written and proved correct in Coq. MetaCoq proves
type checking and *erasure* correct inside Coq ("Coq Coq correct!"); Forster,
Sozeau and Tabareau [42] give a verified extraction pipeline to OCaml with a
correctness theorem, and show that only first-order results are safe to
interoperate with (higher-order interop can misbehave or segfault). Lesson:
even in the system that has extraction, the trustworthy version of it is
recent (2020–2024) and restricted; most Coq practice before that trusted the
extractor and the OCaml compiler, which is the Lean situation with
`native_decide` (trust the Lean compiler).

Isabelle's code generator [45], [46]. The principle is shallow embedding: "the
carrier of a generated program's semantics are equational theorems from the
logic"; the generated program is a higher-order rewrite system each of whose
steps "can be simulated in the logic, which guarantees partial correctness".
The tunable part is the set of *code equations*: by proving an alternative
equation `f x = (fast implementation) x` and declaring it `[code]`, the user
replaces the definition used for code generation without touching the logical
definition. Lammich's refinement framework [21] automates this from abstract
sets and maps to efficient structures. The Isabelle route therefore makes
"faithful to the theory but built for efficiency" a *proof obligation with a
fixed shape* (a code equation) rather than a discipline. Termination: Isabelle
functions defined by `function` with a termination proof generate code from
their recursion equations; the termination proof is never part of the code.
Partial correctness only: generated code that diverges proves nothing, which
is the same trade our certificates make (a producer that fails produces no
certificate).

CakeML / HOL4 [47], [48]. Myreen and Owens's proof-producing synthesis turns a
HOL function into CakeML source with a HOL theorem that the source implements
the function; CakeML's compiler is verified down to machine code. cake_lpr [16]
is the application to a certificate checker. This is the far end of the
faithfulness axis: the fast code is produced *with* its own correctness
theorem, per function. There is no Lean counterpart.

What transfers to Lean, which has no extraction. In every system above, "erase
the termination argument at run time" is the composition of two facts: (i) the
termination argument is a proof (in `Prop`, or an accessibility predicate), and
(ii) the code path (extraction, code equations, synthesis) drops proofs. Lean's
compiler also drops proofs and `Prop`-typed data (the compiler erases
propositions and types; this is why `native_decide` can be fast), so for
*compiled* Lean code the erasure is already automatic: a `termination_by` and
`decreasing_by` cost nothing at run time. The failure in lax-logic was not an
erasure failure; it was that the bound had been put *in the computation*
(`decideFuel` computes the size of the sequent space as a `Nat` and feeds it to
the search), i.e. in `Type`, where no erasure can remove it. More precisely,
two costs are on record, both at run time: (a) materialising the domain the
bound is computed from (`decideFuel` builds the whole formula space in order to
count it; measured on a provable sequent), and (b) the fuelled engine exploring
failing branches down to the fuel depth (it "ground for minutes" on refutable
goals, where the fuel-free `G4cTm.find` took 0 ms). For (a) the rule is stronger
than "keep fuel out of `Type`": **the run must never materialise the domain a
measure is computed from.** For (b) it is the certificate route: an untrusted,
fuel-free producer whose output alone is checked. The Rocq
literature's advice is identical: keep bounds and measures in `Prop`, or as
accessibility predicates, never as fuel computed in `Type`, and if fuel is
needed for structural recursion make it a cheap over-approximation supplied at
call time (as `find` does with 10,000) with the exact bound appearing only in
the completeness theorem. Faithfulness of the fast code to the theory is
established, across the systems, in three ways: a proved equation (Isabelle
code equations, Lean `csimp`, our refinement theorems); a verified translation
(CertiCoq, MetaCoq erasure, CakeML synthesis); or trust (Rocq `Extract
Constant`, Lean `implemented_by`, Lean `native_decide`). Only the first is
available to us without extending the trusted base, so the harness should
make it the default shape.

## Q4. Our practice against the prior art

Already known, and under what names:
- Untrusted producer, literal certificate, Boolean checker proved sound,
  kernel verdict: *certifying algorithm* [1] with a *verified checker* [2],
  discharged by *proof by reflection* [5], [6]. In model checking specifically:
  *certified model checking* [17], [19]; bisimulation certificates [20].
- "Search proposes, a proved checker decides", checked after each run:
  *translation validation* [10], [11].
- "Add a witness rather than waiting": the DRAT to LRAT principle [14], [15].
- "One evaluator, each checker a small refinement", and the theorem
  `certCheck cert = true ⇒ checkG = checkC`: *data refinement* [21] /
  *code equations* [45]; in Lean, `@[csimp]` [28].
- Fuel out of the statement and out of the decision path (lax-logic,
  2026-07-19 and 2026-08-26): *erasure of termination arguments* [38], [39].
- "Watch a gate fail once" (each checker seen rejecting a corrupted
  certificate): negative testing of the checker; Alkassar et al. [2] and the
  SAT checkers do the same with corrupted proofs, without a special name.
- Axiom pin and daily sweep: the Lean reference's own recommendation [24]
  (`#print axioms`, dedicated axioms for native tactics, external checkers).

Not required by the literature but done here: proving the *producer* complete
(C-occ″, G1 as a hypothesis of `certBisimSound`). The certifying-algorithm
paradigm needs only soundness of the checker; a reachability certificate [19]
needs closure, not completeness, because missing states only make the
certificate fail. A bisimulation certificate is different: a missing move can
make a false bisimulation pass, so exactness of the graph is a soundness
hypothesis. Heath and Miller [20] handle this by having the certificate for
bisimulation be a relation that the checker closes *itself* over the
transition relation, which presupposes the checker can enumerate successors;
we instead prove that the matcher's enumeration is exact. Either is sound; ours
needs a 5,000-line completeness proof, theirs needs a checker that searches.
I did not find a published case where producer completeness was proved for
exactly this reason, but I also would not call it novel: it is the obvious
consequence of certifying a universal property.

Gaps (what the established approaches do that we do not):
1. Independent re-checking. Lean's reference [24] recommends `lean4checker`
   (and Lean4Lean [35] exists) for proofs that must survive adversarial
   scrutiny. Our protocol stops at `#print axioms` in the elaborator. Cheap to
   add.
2. A certificate-format specification separate from the Lean type, with a
   second checker. Every SAT format has several checkers [13]–[16], [22]; ours
   has one, and its spec is the Lean structure.
3. Measured kernel profiles. `logic-checking-plan.md` gives one measurement
   (`ssR.length = 12` not finishing in ten minutes) and an estimate ("about n
   seconds of kernel time"). The SAT and bv_decide papers report checker time
   as a function of certificate size [14], [22], [33]. We have no table of
   kernel time against states and edges, so the "minutes means a missing
   witness" rule has no calibrated threshold.
4. Streaming and incremental checking [34]. Our certificates are one literal
   in one file checked by one `decide`; at 160 states this is fine, at 10,000
   it will not be, and the kernel has no sharing across `decide` calls.
5. A fixed shape for faithfulness. Isabelle's code equations and Lean's
   `csimp` give the fast-versus-specification equation a declared form that
   tools can find. Our refinement theorems have no common name or attribute.
6. Verified erasure of bounds. In Rocq this is automatic. In Lean the
   discipline "bounds in Prop or in the completeness theorem only" is enforced
   by review (Matthew's question "why is fuel in the statement at all?"), not
   by a tool. A lint that flags `Nat`-valued bounds computed from cardinalities
   inside a `Decidable` instance would be new, as far as I searched.

Searches made for the originality questions: "certifying algorithm verified
checker", "proof by reflection kernel decide", "translation validation
matcher", "bisimulation certificate verified checker", "certified model
checking certificate Isabelle Coq Lean", "verified extraction Lean 4",
"program extraction Lean", "Lean fuel well-founded recursion kernel reduction",
"LRAT Lean verified checker", "erasure termination argument extraction". The
hits are the bibliography above.

PROVED / REFUTED / OPEN, as far as this survey can say:
- PROVED (in the repositories, per the files): `certBisimSound`,
  `certWeakBisimSound`, the ABP verdicts, `decidablePLL` at
  `[propext, Quot.sound]`, the 442 kernel-checked `Interd` cells.
- REFUTED: the first locus route (kernel `decide` on the explorer) and the
  first lax-logic decision packaging (`decideFuel`) as *efficient* routes, by
  the recorded timings.
- OPEN: whether a lint for run-time bounds is feasible; the kernel-time
  profile; whether a search-based bisimulation checker à la Heath–Miller would
  be cheaper overall than the matcher-completeness proof.

## Q5. Candidate outline of procedures (outline only)

Steps for a new problem, each with its prior-art source.

1. State the theory. Define the semantic property as a Lean `Prop` over the
   library objects, and the statement to be certified as a named
   `…Statement` definition reviewed before any proof. Termination arguments
   and finiteness bounds live here, as theorems. [Bove–Capretta 39; locus
   "statements first"]
2. Refute first. Look for a countermodel of the statement with the cheapest
   available search; a kernel-checked `¬ Statement` ends the step.
   [review-logic §1; no external source needed]
3. Design the certificate. Decide what the producer must hand over so that
   the checker performs no search: every existential in the property becomes a
   listed witness (renumbering, path, index); every universal becomes a
   finite table the checker iterates. Write the format down in prose, not only
   as the Lean type. [McConnell et al. 1 (witness property); LRAT 14 (hints);
   Heath–Miller 20 (certificates for reachability and bisimulation)]
4. Write the checker as a structurally recursive Boolean function over literal
   data (`Nat` indices, lists), avoiding well-founded recursion, `partial`, and
   `Eq.rec` in anything the kernel must reduce. Reuse one evaluator across
   checkers where possible. [Lean reference 25; `decide` docstring 27;
   logic-checking-plan]
5. Prove soundness: `check cert = true → Property`. Where the property is
   universal (bisimulation, invariance), state and prove the exactness
   hypothesis on the producer separately, or redesign the certificate so the
   checker closes the relation itself. [Alkassar et al. 2; CertBisim.lean;
   Heath–Miller 20]
6. Prove the refinement to the library meaning in the fixed shape
   "efficient evaluator equals specification evaluator under `check = true`",
   and keep that shape recognisable (one name, one attribute, or one file
   section). [Isabelle code equations 45; Lammich 21; Lean `csimp` 28]
7. Build the producer for speed, compiled, untrusted, with no fuel or bound in
   the statement it emits and with any bound it needs internally supplied as
   a cheap over-approximation at call time. Its output is a generated Lean
   source file of literals, with the generating script committed beside it.
   [Rocq extraction 38 (bounds are erased); lax-logic PROGRESS §10 and
   HANDOFF §2026-08-26e; logic-checking-plan]
8. Check in the kernel: `by decide +kernel` on `check cert = true`, then the
   soundness and refinement theorems applied. Pin axioms per file. [Boutin 5;
   Barendregt–Barendsen 6; Lean reference 24]
9. Negative test: corrupt the certificate once and watch the gate reject it.
   [review-logic §1; practice in 2, 14]
10. Measure: record kernel time against certificate size; if the time is
    out of proportion, return to step 3 and add a witness. [LRAT 14; bv_decide
    22; PBLean 33 report such measurements]
11. Re-check externally: run `lean4checker` (or Lean4Lean) on the module.
    [Lean reference 24; Carneiro 35]

Parameters along which developments differ (Matthew's addition), and which
systems already expose them:

- Kind of certificate. Witness for an existential (a match, a renumbering, a
  path); closure set or invariant for a safety property (reachable set closed
  under successors [19]; inductive invariant [17]); relation for an
  equivalence (bisimulation relation plus answering moves [20],
  `CertBisim.lean`); proof trace (LRAT [14], VeriPB [33], Lean proof terms
  printed as source in `tools/RCellsGen.lean`). Heath and Miller's "clerks and
  experts" are a framework whose explicit purpose is to parameterise the
  certificate format; the SAT world parameterises by hint density (DRAT
  without hints, LRAT with hints, GRAT with its own enrichment).
- Checker evaluation route. Kernel reduction (`decide +kernel`; Coq
  `compute`), compiled evaluation under an axiom (`decide +native`,
  `bv_decide` [23], PBLean [33]; Coq `native_compute`), a trusted reduction
  machine (Coq `vm_compute` [8]), or evaluation outside the prover with a
  verified binary (cake_lpr [16]). Lean exposes this as a flag on `decide`;
  Coq as three tactics; Isabelle as `eval` versus `code_simp` versus
  `normalization`.
- Axiom policy. What the verdict may depend on: `[propext, Quot.sound]` only
  (ours), plus `Classical.choice` (Mathlib's norm), plus compiler trust
  (`Lean.ofReduceBool`, or the per-proof axioms, present by Lean 4.31 [24]). Lean
  exposes it through `#print axioms` and the dedicated native axioms; Mathlib
  exposes it as a contribution rule (no `native_decide` [32]); the Rocq manual
  exposes the analogue for extraction (axioms must be realised, and
  inconsistent axioms yield wrong code [38]).
- Size of the state or search. Determines whether one `decide` on one literal
  suffices (ours, hundreds of states), whether the certificate must be split
  or streamed (lrat-catcher [34], with a resumable checker state), and whether
  explicit proof terms are feasible at all (PBLean [33]: not at tens of
  thousands of steps).
- Termination discipline of the checker and of the producer. Structural
  (reduces in the kernel), well-founded (does not reduce definitionally [25];
  fine for compiled producers), fuel (structural recursion on a `Nat`;
  soundness at every fuel, completeness at a sufficient fuel, as in
  `LJF/OFuel.lean` and `LaxLogic/PLL/G4/G4Dec.lean`), or `partial` (opaque to the kernel,
  compiled only). Lean exposes all four as definition forms; Rocq exposes
  structural versus `Program`/`Function` with accessibility, and erases the
  latter's proofs at extraction [38]; Bove–Capretta is the theory [39].
- How faithfulness of the fast implementation is established. Proved equation
  (Isabelle code equations [45], Lean `csimp` [28], our refinement theorems);
  verified translation (CertiCoq [40], MetaCoq erasure [41], verified
  extraction [42], CakeML synthesis [47]); trusted replacement (Rocq
  `Extract Constant` [38], Lean `implemented_by` [29]); or no claim at all,
  the producer being untrusted and only its output checked (translation
  validation [10]; our producers). Lean exposes the first and third as
  attributes, and the fourth is simply the absence of any attribute.
- Two further axes the prior art shows: whether producer *completeness* is
  needed (universal properties) or only checker soundness (existential and
  safety properties), discussed in Q4; and whether the certificate is
  committed as an artifact (ours, with the generating script) or regenerated
  per run (the SAT and bv_decide practice).

A generic harness would fix the step list above and take these axes as its
parameters; the defaults for locus-style work are: witness or relation
certificate, kernel route, `[propext, Quot.sound]`, single literal file,
structural checker with fuel only where structural recursion is impossible,
faithfulness by a proved refinement equation.

## Open questions

1. Kernel time profile. What does the kernel actually spend time on when
   reducing `wbisimCheck` on the ABP certificate: list indexing, `Nat`
   comparison, `DecidableEq` on bigraph nodes, or the `perm` equations? No
   measurement exists; the answer determines where a witness helps.
2. Whether the kernel's special support for `Nat` literals [26] can be
   exploited further by encoding more of the certificate as numbers (e.g.
   packed indices) rather than nested lists.
3. Whether a search-based bisimulation checker (the checker closes the
   relation over the matcher's successors, as in Heath–Miller [20]) would be
   cheaper in total than proving matcher completeness for each new rule set.
4. Whether `@[csimp]`-registered refinement equations could let the *same*
   definition serve as the kernel checker and as the fast compiled producer,
   removing the hand-written duplicate.
5. A lint for run-time bounds: can a simple check over a `Decidable` instance
   or a `def` detect `Nat` values computed from cardinalities of materialised sets on
   the evaluation path? Nothing found in the literature.
6. The four-colour reference [9] remains UNVERIFIED; replace it or drop it
   before any external use of this survey.
