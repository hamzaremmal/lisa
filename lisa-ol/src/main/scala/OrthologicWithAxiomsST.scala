/*import collection.mutable.Map as mMap
import lisa.fol.FOL as F
import lisa.maths.settheory.SetTheory.*
import lisa.automation.kernel.CommonTactics.Definition
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{ProofSequentTactic, ProofTactic}

object OrthologicWithAxiomsST extends lisa.Main:

  // ortholattice signature
  val S, T, U = variable
  val <= = variable
  val n, u, not = variable
  val `0`, `1` = variable

  // ortholattice elements
  val v, w, x, y, z = variable

  // needed for subst in defs from maths.SetTheory
  val a, b, c, f, r, t = variable

  // ==============================================================================================
  // ========================================== DSL ===============================================
  // ==============================================================================================

  given zero2term: Conversion[0, Term] with
    override inline def apply(x: 0): Term = `0`

  given one2term: Conversion[1, Term] with
    override inline def apply(x: 1): Term = `1`

  extension(left: Term)
    inline def <=(right: Term): Formula = pair(left, right) ∈ OrthologicWithAxiomsST.<=
    inline def n(right: Term): Term = app(OrthologicWithAxiomsST.n, pair(left, right))
    inline def u(right: Term): Term = app(OrthologicWithAxiomsST.u, pair(left, right))
    inline def x(right: Term): Term = cartesianProduct(left, right)
    inline def unary_! = app(OrthologicWithAxiomsST.not, left)

  // ==============================================================================================

  inline def forallInU(xs: Variable*)(f: Formula): Formula =
    xs.foldRight(f) { (x, g) => ∀(x, (x ∈ U) ==> g) }

  inline def inU(xs: Term*): Seq[F.Formula] = xs.map(_ ∈ U)

  // CHECK is actually using the def argument
  val p1 = DEF(U, <=) --> forallInU(x) { x <= x }
  val p2 = DEF(U, <=) --> forallInU(x, y, z) { (x <= y) /\ (y <= z) ==> x <= z }
  val p3a = DEF(U, <=, `0`) --> forallInU(x) { 0 <= x }
  val p3b = DEF(U, <=, `1`) --> forallInU(x) { x <= 1 }
  val p4a = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= x }
  val p5a = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= y }
  val p4b = DEF(U, <=, u) --> forallInU(x, y) { x <= (x u y) }
  val p5b = DEF(U, <=, u) --> forallInU(x, y) { y <= (x u y) }
  val p6a = DEF(U, <=, n) --> forallInU(x, y, z) { (x <= y) /\ (x <= z) ==> x <= (y n z) }
  val p6b = DEF(U, <=, u) --> forallInU(x, y, z) { (x <= z) /\ (y <= z) ==> (x u y) <= z }
  val p7a = DEF(U, <=, not) --> forallInU(x) { x <= !(!x) }
  val p7b = DEF(U, <=, not) --> forallInU(x) { !(!x) <= x }
  val p8 = DEF(U, <=, not) --> forallInU(x, y) { x <= y ==> !y <= !x }
  val p9a = DEF(U, <=, n, not, `0`) --> forallInU(x) { (x n !x) <= 0 }
  val p9b = DEF(U, <=, u, not, `1`) --> forallInU(x) { 1 <= (x u !x) }

  // ==============================================================================================
  // ================================== ORTHOLATTICE DEFINITION ===================================
  // ==============================================================================================

  val ortholattice = DEF(U, <=, n, u, not, `0`, `1`) --> And(Seq(
    0 ∈ U, 1 ∈ U,
    relationBetween(<=, U, U),
    functionFrom(not, U, U),
    functionFrom(n, cartesianProduct(U, U), U),
    functionFrom(u, cartesianProduct(U, U), U),
    p1(U, <=),
    p2(U, <=),
    p3a(U, <=, `0`), p3b(U, <=, `1`),
    p4a(U, <=, n), p4b(U, <=, u),
    p5a(U, <=, n), p5b(U, <=, u),
    p6a(U, <=, n), p6b(U, <=, u),
    p7a(U, <=, not), p7b(U, <=, not),
    p8(U, <=, not),
    p9a(U, <=, n, not, `0`), p9b(U, <=, u, not, `1`)
  ))

  inline def isO = ortholattice(U, <=, n, u, not, 0, 1)

  // ==============================================================================================
  // =================================== REFORMULATE AXIOMS =======================================
  // ==============================================================================================

  /** STATUS: DONE */
  val lemmaForP1 = Lemma((isO, x ∈ U) |- x <= x):
    assume(isO)
    have(∀(x, (x ∈ U) ==> x <= x)) by Tautology.from(ortholattice.definition, p1.definition)
    val step1 = thenHave(x ∈ U ==> x <= x) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP1

  /** STATUS: DONE */
  val lemmaForP2 = Lemma((isO, x ∈ U, y ∈ U, z ∈ U) |- (x <= y) /\ (y <= z) ==> x <= z):
    assume(isO)
    have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z))))) by Tautology.from(ortholattice.definition, p2.definition)
    val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z)))) by InstantiateForall(x)
    assume(x ∈ U)
    have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z)))) by Tautology.from(step1)
    val step2 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z))) by InstantiateForall(y)
    assume(y ∈ U)
    have(∀(z, (z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z))) by Tautology.from(step2)
    val step3 = thenHave((z ∈ U) ==> ((x <= y) /\ (y <= z) ==> x <= z)) by InstantiateForall(z)
    assume(z ∈ U)
    have(thesis) by Tautology.from(step3)
  end lemmaForP2

  /** STATUS: DONE */
  val lemmaForP3A = Lemma((isO, x ∈ U) |- 0 <= x):
    assume(isO)
    have(∀(x, (x ∈ U) ==> (0 <= x))) by Tautology.from(ortholattice.definition, p3a.definition)
    val step1 = thenHave((x ∈ U) ==> (0 <= x)) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP3A

  /** STATUS: DONE */
  val lemmaForP3B = Lemma((isO, x ∈ U) |- x <= 1):
    assume(isO)
    have(∀(x, (x ∈ U) ==> (x <= 1))) by Tautology.from(ortholattice.definition, p3b.definition)
    val step1 = thenHave((x ∈ U) ==> (x <= 1)) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP3B

  /** STATUS: DONE */
  val lemmaForP6A = Lemma((isO, x ∈ U, y ∈ U, z ∈ U, x <= y, x <= z) |- x <= (y n z)):
    assume(isO)
    val step1 = have((x ∈ U, y ∈ U, z ∈ U) |- (x <= y) /\ (x <= z) ==> x <= (y n z)) subproof :
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))))) by Tautology.from(ortholattice.definition, p6a.definition)
      val step11 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))))) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))))) by Tautology.from(step11)
      val step12 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))) by Tautology.from(step12)
      thenHave((z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))) by InstantiateForall(z)
      have(thesis) by Tautology.from(lastStep)
    val step2 = have((x <= y, x <= z) |- (x <= y) /\ (x <= z)) subproof :
      have((x <= y, x <= z) |- (x <= y, x <= z)) by Restate
      have(thesis) by LeftAnd(lastStep)
    have(thesis) subproof :
      have((x ∈ U, y ∈ U, z ∈ U, (x <= y) /\ (x <= z)) |- x <= (y n z)) by Tautology.from(step1)
      have(thesis) by Cut.withParameters((x <= y) /\ (x <= z))(step2, lastStep)
  end lemmaForP6A

  /** STATUS: DONE */
  val lemmaForP6B = Lemma((isO, x ∈ U, y ∈ U, z ∈ U, x <= z, y <= z) |- (x u y) <= z):
    assume(isO)
    val step1 = have((x ∈ U, y ∈ U, z ∈ U) |- (x <= z) /\ (y <= z) ==> (x u y) <= z) subproof :
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z))))) by Tautology.from(ortholattice.definition, p6b.definition)
      val step11 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)))) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)))) by Tautology.from(step11)
      val step12 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> ((y <= z) /\ (x <= z) ==> (x u y) <= z))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z))) by Tautology.from(step12)
      thenHave((z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)) by InstantiateForall(z)
      have(thesis) by Tautology.from(lastStep)
    val step2 = have((x <= z, y <= z) |- (x <= z) /\ (y <= z)) subproof :
      have((x <= z, y <= z) |- (x <= z, y <= z)) by Restate
      have(thesis) by LeftAnd(lastStep)
    have(thesis) subproof :
      have((x ∈ U, y ∈ U, z ∈ U, (x <= z) /\ (y <= z)) |- (x u y) <= z) by Tautology.from(step1)
      have(thesis) by Cut.withParameters((x <= z) /\ (y <= z))(step2, lastStep)
  end lemmaForP6B

  /** STATUS: DONE */
  val lemmaForP7A = Lemma((isO, x ∈ U) |- x <= !(!x)):
    assume(isO)
    have(∀(x, (x ∈ U) ==> x <= !(!x))) by Tautology.from(ortholattice.definition, p7a.definition)
    val step1 = thenHave((x ∈ U) ==> x <= !(!x)) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP7A

  /** STATUS: DONE */
  val lemmaForP7B = Lemma((isO, x ∈ U) |- !(!x) <= x):
    assume(isO)
    have(∀(x, (x ∈ U) ==> !(!x) <= x)) by Tautology.from(ortholattice.definition, p7b.definition)
    val step1 = thenHave((x ∈ U) ==> !(!x) <= x) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP7B

  /** STATUS: DONE */
  val lemmaForP8 = Lemma((isO, x ∈ U, y ∈ U, x <= y) |- !y <= !x):
    assume(isO)
    have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> (x <= y ==> !y <= !x)))) by Tautology.from(ortholattice.definition, p8.definition)
    val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> (x <= y ==> !y <= !x))) by InstantiateForall(x)
    assume(x ∈ U)
    have(∀(y, (y ∈ U) ==> (x <= y ==> !y <= !x))) by Tautology.from(step1)
    val step2 = thenHave((y ∈ U) ==> (x <= y ==> !y <= !x)) by InstantiateForall(y)
    assume(y ∈ U)
    have(thesis) by Tautology.from(step2)
  end lemmaForP8

  /** STATUS: DONE */
  val lemmaForP9A = Lemma((isO, x ∈ U) |- (x n !x) <= 0):
    assume(isO)
    have(∀(x, (x ∈ U) ==> (x n !x) <= 0)) by Tautology.from(ortholattice.definition, p9a.definition)
    val step1 = thenHave((x ∈ U) ==> (x n !x) <= 0) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP9A

  /** STATUS: DONE */
  val lemmaForP9B = Lemma((isO, x ∈ U) |- 1 <= (x u !x)):
    assume(isO)
    have(∀(x, (x ∈ U) ==> 1 <= (x u !x))) by Tautology.from(ortholattice.definition, p9b.definition)
    val step1 = thenHave((x ∈ U) ==> 1 <= (x u !x)) by InstantiateForall(x)
    assume(x ∈ U)
    have(thesis) by Tautology.from(step1)
  end lemmaForP9B

  // ==============================================================================================
  // ======================================== LEMMAS ==============================================
  // ==============================================================================================

  /** STATUS: DONE */
  val appInCodomain = Lemma((functionFrom(f, S, T), (x ∈ S)) |- (app(f, x) ∈ T)):
    assume(functionFrom(f, S, T), (x ∈ S))

    val functionalOverU = have(functionalOver(f, S)) subproof :
      val s1 = have(f ∈ setOfFunctions(S, T)) by Tautology.from(functionFrom.definition of(x := S, y := T))
      have(∀(t, in(t, setOfFunctions(S, T)) <=> (in(t, powerSet(cartesianProduct(S, T))) /\ functionalOver(t, S)))) by Definition(setOfFunctions, setOfFunctionsUniqueness)(S, T)
      thenHave(in(f, setOfFunctions(S, T)) <=> (in(f, powerSet(cartesianProduct(S, T))) /\ functionalOver(f, S))) by InstantiateForall(f)
      have(thesis) by Tautology.from(lastStep, s1)
    end functionalOverU
    val appInRange = have(app(f, x) ∈ relationRange(f)) subproof :
      have(pair(x, app(f, x)) ∈ f) by Tautology.from(functionalOverU, functionalOverApplication of(x := S, a := x, b := app(f, x)))
      val s1 = thenHave(∃(a, pair(a, app(f, x)) ∈ f)) by RightExists
      have(∀(t, in(t, relationRange(f)) <=> ∃(a, in(pair(a, t), f)))) by Definition(relationRange, relationRangeUniqueness)(f)
      val s2 = thenHave((app(f, x) ∈ relationRange(f)) <=> ∃(a, in(pair(a, app(f, x)), f))) by InstantiateForall(app(f, x))
      have(thesis) by Tautology.from(s1, s2)
    end appInRange
    val inRangeImpliesInCodomain = have(z ∈ relationRange(f) |- z ∈ T) subproof :
      have(relationRange(f) ⊆ T) by Tautology.from(functionImpliesRangeSubsetOfCodomain of(x := S, y := T))
      thenHave(∀(z, (z ∈ relationRange(f)) ==> (z ∈ T))) by Substitution.ApplyRules(subsetAxiom of(x := relationRange(f), y := T, z := app(f, x)))
      thenHave(thesis) by InstantiateForall(z)
    end inRangeImpliesInCodomain

    have(thesis) by Tautology.from(appInRange, inRangeImpliesInCodomain of (z := app(f, x)))
  end appInCodomain

  /** STATUS: DONE */
  val cartesianProductElement = Lemma((x ∈ U, y ∈ U) |- pair(x, y) ∈ (U x U)):
    val step1 = have(pair(x, y) ∈ (U x U) <=> x ∈ U /\ y ∈ U) by Restate.from(pairInCartesianProduct of(a := x, b := y, x := U, y := U))
    assume(x ∈ U)
    assume(y ∈ U)
    have(thesis) by Tautology.from(step1)
  end cartesianProductElement

  /** STATUS: DONE */
  val joinIsClosed = Lemma((isO, (x ∈ U) /\ (y ∈ U)) |- (x u y) ∈ U):
    val step1 = have((isO, x ∈ U, y ∈ U) |- (x u y) ∈ U) subproof:
      val step1 = have(isO |- functionFrom(u, U x U, U)) by Tautology.from(ortholattice.definition)
      val step2 = have((functionFrom(u, U x U, U), pair(x, y) ∈ (U x U)) |- (x u y) ∈ U) by Restate.from(appInCodomain of(f := u, S := (U x U), T := U, x := pair(x, y)))
      val step3 = have((isO, pair(x, y) ∈ (U x U)) |- (x u y) ∈ U) by Cut.withParameters(functionFrom(u, (U x U), U))(step1, step2)
      have(thesis) by Cut.withParameters(pair(x, y) ∈ (U x U))(cartesianProductElement, step3)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- (x ∈ U, y ∈ U)) subproof:
        have((x ∈ U, y ∈ U) |- (x ∈ U, y ∈ U)) by Restate
        thenHave(thesis) by LeftAnd
    have(thesis) by Tautology.from(step1, step2)
  end joinIsClosed

  /** STATUS: DONE */
  val meetIsClosed = Lemma((isO, (x ∈ U) /\ (y ∈ U)) |- (x n y) ∈ U):
    val step1 = have((isO, x ∈ U, y ∈ U) |- (x n y) ∈ U) subproof:
      val step1 = have(isO |- functionFrom(n, U x U, U)) by Tautology.from(ortholattice.definition)
      val step2 = have((functionFrom(n, U x U, U), pair(x, y) ∈ (U x U)) |- (x n y) ∈ U) by Restate.from(appInCodomain of(f := n, S := (U x U), T := U, x := pair(x, y)))
      val step3 = have((isO, pair(x, y) ∈ (U x U)) |- (x n y) ∈ U) by Cut.withParameters(functionFrom(n, (U x U), U))(step1, step2)
      have(thesis) by Cut.withParameters(pair(x, y) ∈ (U x U))(cartesianProductElement, step3)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- (x ∈ U, y ∈ U)) subproof:
      have((x ∈ U, y ∈ U) |- (x ∈ U, y ∈ U)) by Restate
      thenHave(thesis) by LeftAnd
    have(thesis) by Tautology.from(step1, step2)
  end meetIsClosed

  /** STATUS: DONE */
  val negationIsClosed = Lemma((isO, x ∈ U) |- !x ∈ U):
    val step1 = have(isO |- functionFrom(not, U, U)) by Tautology.from(ortholattice.definition)
    val step2 = have((functionFrom(not, U, U), x ∈ U) |- !x ∈ U) by Restate.from(appInCodomain of(f := not, S := U, T := U))
    have(thesis) by Cut.withParameters(functionFrom(not, U, U))(step1, step2)
  end negationIsClosed

  /** STATUS: DONE */
  val doubleNegationIsClosed = Lemma((isO, x ∈ U) |- !(!x) ∈ U):
    val step1 = have(isO +: inU(x) |- inU(!x)) by Restate.from(negationIsClosed)
    val step2 = have(isO +: inU(!x) |- inU(!(!x))) by Restate.from(negationIsClosed of (x := !x))
    have(thesis) by Cut.withParameters(!x ∈ U)(step1, step2)
  end doubleNegationIsClosed

  /** STATUS: DONE */
  val zeroInOrtholattice = Lemma(isO |- 0 ∈ U):
    have(thesis) by Tautology.from(ortholattice.definition)
  end zeroInOrtholattice

  /** STATUS: DONE */
  val oneInOrtholattice = Lemma(isO |- 1 ∈ U):
    have(thesis) by Tautology.from(ortholattice.definition)
  end oneInOrtholattice

  /** STATUS: DONE */
  val negationOfZeroIsOne2 = Lemma(isO |- !0 <= 1):
    val step1 = have((isO, !0 ∈ U) |- !0 <= 1) by Restate.from(lemmaForP3B of (x := !0))
    val step2 = have((isO, 0 ∈ U) |- !0 <= 1) by Cut.withParameters(!0 ∈ U)(negationIsClosed of (x := 0), step1)
    have(thesis) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step2)
  end negationOfZeroIsOne2

  /** STATUS: DONE */
  val negationOfOneIsZero1 = Lemma(isO |- 0 <= !1):
    val step1 = have((isO, !1 ∈ U) |- 0 <= !1) by Restate.from(lemmaForP3A of (x := !1))
    val step2 = have((isO, 1 ∈ U) |- 0 <= !1) by Cut.withParameters(!1 ∈ U)(negationIsClosed of (x := 1), step1)
    have(thesis) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step2)
  end negationOfOneIsZero1

  /** STATUS: DONE */
  val negationOfZeroIsOne1 = Lemma(isO |- 1 <= !0):
    assume(isO)
    val step1 = have(!(!1) <= !0) subproof :
      val step11 = have((0 ∈ U, !1 ∈ U, 0 <= !1) |- !(!1) <= !0) by Restate.from(lemmaForP8 of(x := 0, y := !1))
      val step12 = have((!1 ∈ U, 0 <= !1) |- !(!1) <= !0) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step11)
      val step13 = have((!1 ∈ U) |- !(!1) <= !0) by Cut.withParameters(0 <= !1)(negationOfOneIsZero1, step12)
      val step14 = have((1 ∈ U) |- !(!1) <= !0) by Cut.withParameters(!1 ∈ U)(negationIsClosed of (x := 1), step13)
      have(thesis) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step14)
    val step2 = have(1 <= !(!1)) subproof :
      val step21 = have(1 ∈ U |- 1 <= !(!1)) by Rewrite(lemmaForP7A of (x := 1))
      have(thesis) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step21)
    val step3 = have((1 <= !(!1)) /\ (!(!1) <= !0)) by RightAnd(step1, step2)
    have(thesis) subproof :
      val step41 = have((1 ∈ U, !(!1) ∈ U, !0 ∈ U, (1 <= !(!1)) /\ (!(!1) <= !0)) |- 1 <= !0) by Tautology.from(lemmaForP2 of(x := 1, y := !(!1), z := !0))
      val step42 = have((1 ∈ U, !(!1) ∈ U, !0 ∈ U) |- 1 <= !0) by Cut.withParameters((1 <= !(!1)) /\ (!(!1) <= !0))(step3, step41)
      val step43 = have((1 ∈ U, !0 ∈ U) |- 1 <= !0) by Cut.withParameters(!(!1) ∈ U)(doubleNegationIsClosed of (x := 1), step42)
      val step44 = have(!0 ∈ U |- 1 <= !0) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step43)
      val step45 = have(0 ∈ U |- 1 <= !0) by Cut.withParameters(!0 ∈ U)(negationIsClosed of (x := 0), step44)
      have(thesis) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step45)
  end negationOfZeroIsOne1

  /** STATUS: DONE */
  val negationOfOneIsZero2 = Lemma(isO |- !1 <= 0):
    assume(isO)
    val step1 = have(!1 <= !(!0)) subproof :
      val step11 = have((!0 ∈ U, 1 ∈ U, !0 <= 1) |- !1 <= !(!0)) by Restate.from(lemmaForP8 of(x := !0, y := 1))
      val step12 = have((!0 ∈ U, 1 ∈ U) |- !1 <= !(!0)) by Cut.withParameters(!0 <= 1)(lemmaForP3B of (x := !0), step11)
      val step13 = have(!0 ∈ U |- !1 <= !(!0)) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step12)
      val step14 = have(0 ∈ U |- !1 <= !(!0)) by Cut.withParameters(!0 ∈ U)(negationIsClosed of (x := 0), step13)
      have(thesis) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step14)
    val step2 = have(!(!0) <= 0) subproof :
      val step21 = have(0 ∈ U |- !(!0) <= 0) by Rewrite(lemmaForP7B of (x := 0))
      have(thesis) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step21)
    val step3 = have((!1 <= !(!0)) /\ (!(!0) <= 0)) by RightAnd(step1, step2)
    have(thesis) subproof :
      val step41 = have((!1 ∈ U, !(!0) ∈ U, 0 ∈ U, (!1 <= !(!0)) /\ (!(!0) <= 0)) |- !1 <= 0) by Tautology.from(lemmaForP2 of(x := !1, y := !(!0), z := 0))
      val step42 = have((!1 ∈ U, !(!0) ∈ U, 0 ∈ U) |- !1 <= 0) by Cut.withParameters((!1 <= !(!0)) /\ (!(!0) <= 0))(step3, step41)
      val step43 = have((!1 ∈ U, 0 ∈ U) |- !1 <= 0) by Cut.withParameters(!(!0) ∈ U)(doubleNegationIsClosed of (x := 0), step42)
      val step44 = have(!1 ∈ U |- !1 <= 0) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step43)
      val step45 = have(1 ∈ U |- !1 <= 0) by Cut.withParameters(!1 ∈ U)(negationIsClosed of (x := 1), step44)
      have(thesis) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step45)
  end negationOfOneIsZero2

  // ==============================================================================================
  // ============================================ RULES ===========================================
  // ==============================================================================================

  /** STATUS: DONE */
  val hyp = Theorem(isO +: inU(x) |- x <= x):
    val impl = have(isO |- (x ∈ U ==> x <= x)) subproof :
      assume(isO)
      have(∀(x, x ∈ U ==> x <= x)) by Tautology.from(ortholattice.definition, p1.definition)
      thenHave(thesis) by InstantiateForall(x)
    end impl
    have(thesis) by Tautology.from(impl)
  end hyp

  /** STATUS: DONE */
  val cut = Theorem(isO +: inU(x, y, z) :+ (x <= y) :+ (y <= z) |- (x <= z)) :
    have(thesis) by Tautology.from(lemmaForP2)
  end cut

  /** STATUS: DONE */
  val weaken1 = Theorem(isO +: inU(x, y) :+ (x <= 0) |- x <= y):
    val step1 = have(isO +: inU(y) |- 0 <= y) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> 0 <= x)) by Tautology.from(ortholattice.definition, p3a.definition)
      thenHave((x ∈ U) ==> 0 <= x) by InstantiateForall(x)
      have(thesis) by Tautology.from(lastStep of (x := y))
    val step2 = have(isO +: inU(x, y, 0) :+ (x <= 0) :+ (0 <= y) |- (x <= y)) subproof :
      have(thesis) by Restate.from(cut of(y := 0, z := y))
    val step3 = have(isO +: inU(x, y) :+ (x <= 0) :+ (0 <= y) |- x <= y) subproof :
      have(thesis) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, step2)
    have(thesis) by Cut.withParameters(0 <= y)(step1, step3)
  end weaken1

  /** STATUS: DONE */
  val weaken2 = Theorem(isO +: inU(x, y) :+ (1 <= y) |- x <= y) :
    val step1 = have(isO +: inU(x) |- x <= 1) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> x <= 1)) by Tautology.from(ortholattice.definition, p3b.definition)
      thenHave((x ∈ U) ==> x <= 1) by InstantiateForall(x)
      have(thesis) by Tautology.from(lastStep)
    val step2 = have(isO +: inU(x, y, 1) :+ (x <= 1) :+ (1 <= y) |- (x <= y)) subproof :
      have(thesis) by Restate.from(cut of(y := 1, z := y))
    val step3 = have(isO +: inU(x, y) :+ (x <= 1) :+ (1 <= y) |- x <= y) subproof :
      have(thesis) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, step2)
    have(thesis) by Cut.withParameters(x <= 1)(step1, step3)
  end weaken2

  // x^L x^L |- x^L
  /** STATUS: DONE */
  val contraction1 = Theorem(isO +: inU(x) :+ (x <= !x) |- x <= 0):
    assume(isO)
    val step1 = have((x ∈ U, x <= !x) |- x <= (x n !x)) subproof:
      have((x ∈ U, !x ∈ U, x <= x, x <= !x) |- x <= (x n !x)) by Restate.from(lemmaForP6A of (x := x, y := x, z := !x))
      have((x ∈ U, !x ∈ U, x <= !x) |- x <= (x n !x)) by Cut.withParameters(x <= x)(lemmaForP1, lastStep)
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, lastStep)
    val step2 = have((x ∈ U, x <= (x n !x), (x n !x) <= 0) |- x <= 0) subproof:
      have((x ∈ U, (x n !x) ∈ U, 0 ∈ U, x <= (x n !x), (x n !x) <= 0) |- x <= 0) by Restate.from(cut of (x := x, y := (x n !x), z := 0))
      have((x ∈ U, (x n !x) ∈ U, x <= (x n !x), (x n !x) <= 0) |- x <= 0) by Cut.withParameters(0 ∈ U)(zeroInOrtholattice, lastStep)
      have((x ∈ U, !x ∈ U, x <= (x n !x), (x n !x) <= 0) |- x <= 0) by Tautology.from(meetIsClosed of (y := !x), lastStep) //Cut.withParameters((x n !x) ∈ U)(joinIsClosed of (y := !x), lastStep)
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, lastStep)
    have(thesis) subproof:
      have((x ∈ U, x <= !x, (x n !x) <= 0) |- x <= 0) by Cut.withParameters(x <= (x n !x))(step1, step2)
      have(thesis) by Cut.withParameters((x n !x) <= 0)(lemmaForP9A, lastStep)
  end contraction1

  // x^R x^R |- x^R
  /** STATUS: DONE */
  val contraction2 = Theorem(isO +: inU(x) :+ (!x <= x) |- 1 <= x):
    assume(isO)
    val step1 = have((x ∈ U, !x <= x) |- (x u !x) <= x) subproof:
      have((x ∈ U, !x ∈ U, x <= x, !x <= x) |- (x u !x) <= x) by Restate.from(lemmaForP6B of (x := x, y := !x, z := x))
      have((x ∈ U, !x ∈ U, !x <= x) |- (x u !x) <= x) by Cut.withParameters(x <= x)(lemmaForP1, lastStep)
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, lastStep)
    val step2 = have((x ∈ U, 1 <= (x u !x), (x u !x) <= x) |- 1 <= x) subproof:
      have((x ∈ U, (x u !x) ∈ U, 1 ∈ U, 1 <= (x u !x), (x u !x) <= x) |- 1 <= x) by Restate.from(cut of (x := 1, y := (x u !x), z := x))
      have((x ∈ U, (x u !x) ∈ U, 1 <= (x u !x), (x u !x) <= x) |- 1 <= x) by Cut.withParameters(1 ∈ U)(oneInOrtholattice, lastStep)
      have((x ∈ U, !x ∈ U, 1 <= (x u !x), (x u !x) <= x) |- 1 <= x) by Tautology.from(joinIsClosed of (y := !x), lastStep) //Cut.withParameters((x u !x) ∈ U)(meetIsClosed of (y := !x), lastStep)
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, lastStep)
    have(thesis) subproof:
      have((x ∈ U, !x <= x, 1 <= (x u !x)) |- 1 <= x) by Cut.withParameters((x u !x) <= x)(step1, step2)
      have(thesis) by Cut.withParameters(1 <= (x u !x))(lemmaForP9B, lastStep)
  end contraction2

  /** STATUS: DONE */
  val leftAnd1 = Theorem(isO +: inU(x, y, z) :+ (x <= z) |- (x n y) <= z) :
    val step1 = have(isO +: inU(x, y, z) |- (x n y) <= x) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x))) by Tautology.from(ortholattice.definition, p4a.definition)
      val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x)) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> (x n y) <= x)) by Tautology.from(step1)
      val step2 = thenHave((y ∈ U) ==> (x n y) <= x) by InstantiateForall(y)
      assume(y ∈ U)
      have(thesis) by Tautology.from(step2)
    val step2 = have(isO +: inU(x, (x n y), z) :+ ((x n y) <= x) :+ (x <= z) |- (x n y) <= z) subproof :
      have(thesis) by Restate.from(cut of (x := (x n y), y := x))
    val step3 = have(isO +: inU(x, y, z) :+ ((x n y) <= x) :+ (x <= z) |- (x n y) <= z) subproof :
      have(thesis) by Tautology.from(meetIsClosed, step2) // Cut.withParameters((x n y) ∈ U)(joinIsClosed, step2)
    have(thesis) by Cut.withParameters((x n y) <= x)(step1, step3)
  end leftAnd1

  /** STATUS: DONE */
  val leftAnd2 = Theorem(isO +: inU(x, y, z) :+ (y <= z) |- (x n y) <= z) :
    val step1 = have(isO +: inU(x, y, z) |- (x n y) <= y) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= y))) by Tautology.from(ortholattice.definition, p5a.definition)
      val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= y)) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> (x n y) <= y)) by Tautology.from(step1)
      val step2 = thenHave((y ∈ U) ==> (x n y) <= y) by InstantiateForall(y)
      assume(y ∈ U)
      have(thesis) by Tautology.from(step2)
    val step2 = have(isO +: inU((x n y), y, z) :+ ((x n y) <= y) :+ (y <= z) |- (x n y) <= z) subproof:
      have(thesis) by Restate.from(cut of(x := (x n y)))
    val step3 = have(isO +: inU(x, y, z) :+ ((x n y) <= y) :+ (y <= z) |- (x n y) <= z) subproof :
      have(thesis) by Tautology.from(meetIsClosed, step2)// Cut.withParameters((x n y) ∈ U)(joinIsClosed, step2)
    have(thesis) by Cut.withParameters((x n y) <= y)(step1, step3)
  end leftAnd2

  /** STATUS: DONE */
  val leftOr = Theorem(isO +: inU(x, y, z) :+ (x <= z) :+ (y <= z) |- (x u y) <= z) :
    val impl = have(isO +: inU(x, y, z) |- (x <= z) /\ (y <= z) ==> (x u y) <= z) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z))))) by Tautology.from(ortholattice.definition, p6b.definition)
      val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)))) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)))) by Tautology.from(step1)
      val step2 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z))) by Tautology.from(step2)
      val step3 = thenHave((z ∈ U) ==> ((x <= z) /\ (y <= z) ==> (x u y) <= z)) by InstantiateForall(z)
      have(thesis) by Tautology.from(step3)
    end impl
    have(thesis) by Tautology.from(impl)
  end leftOr

  /** STATUS: DONE */
  val rightAnd = Theorem(isO +: inU(x, y, z) :+ (x <= y) :+ (x <= z) |- x <= (y n z)):
    val impl = have(isO +: inU(x, y, z) |- (x <= y) /\ (x <= z) ==> x <= (y n z)) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))))) by Tautology.from(ortholattice.definition, p6a.definition)
      val step1 = thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))))) by InstantiateForall(x)
      assume(x ∈ U)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))))) by Tautology.from(step1)
      val step2 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z)))) by Tautology.from(step2)
      val step3 = thenHave((z ∈ U) ==> ((x <= y) /\ (x <= z) ==> x <= (y n z))) by InstantiateForall(z)
      have(thesis) by Tautology.from(step3)
    end impl
    have(thesis) by Tautology.from(impl)
  end rightAnd

  /** STATUS: DONE */
  val rightOr1 = Theorem(isO +: inU(x, y, z) :+ (x <= y) |- x <= (y u z)) :
    val step1 = have(isO +: inU(y, z) |- y <= (y u z)) subproof :
      assume(isO)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> y <= (y u z)))) by Tautology.from(ortholattice.definition, p4b.definition of (x := y, y := z))
      val step1 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> y <= (y u z))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> y <= (y u z))) by Tautology.from(step1)
      val step2 = thenHave((z ∈ U) ==> y <= (y u z)) by InstantiateForall(z)
      have(thesis) by Restate.from(step2)
    val step2 = have(isO +: inU(x, y, z, (y u z)) :+ (x <= y) :+ (y <= (y u z)) |- x <= (y u z)) subproof:
      have(isO +: inU(x, y, (y u z)) :+ (x <= y) :+ (y <= (y u z)) |- x <= (y u z)) by Restate.from(cut of (z := (y u z)))
      thenHave(thesis) by Weakening
    val step3 = have(isO +: inU(x, y, z) :+ (x <= y) :+ (y <= (y u z)) |- x <= (y u z)) subproof:
      have(thesis) by Tautology.from(joinIsClosed of (x := y, y := z), step2)// Cut.withParameters((y u z) ∈ U)(meetIsClosed of (x := y, y := z), step2)
    have(thesis) by Cut.withParameters(y <= (y u z))(step1, step3)
  end rightOr1

  /** STATUS: DONE */
  val rightOr2 = Theorem(isO +: inU(x, y, z) :+ (x <= z) |- x <= (y u z)) :
    val step1 = have(isO +: inU(y, z) |- z <= (y u z)) subproof :
      assume(isO)
      have(∀(y, (y ∈ U) ==> ∀(z, (z ∈ U) ==> z <= (y u z)))) by Tautology.from(ortholattice.definition, p5b.definition of(x := y, y := z))
      val step1 = thenHave((y ∈ U) ==> ∀(z, (z ∈ U) ==> z <= (y u z))) by InstantiateForall(y)
      assume(y ∈ U)
      have(∀(z, (z ∈ U) ==> z <= (y u z))) by Tautology.from(step1)
      val step2 = thenHave((z ∈ U) ==> z <= (y u z)) by InstantiateForall(z)
      have(thesis) by Restate.from(step2)
    val step2 = have(isO +: inU(x, y, z, (y u z)) :+ (x <= z) :+ (z <= (y u z)) |- x <= (y u z)) subproof:
      have(isO +: inU(x, z, (y u z)) :+ (x <= z) :+ (z <= (y u z)) |- x <= (y u z)) by Restate.from(cut of (y:= z, z := (y u z)))
      thenHave(thesis) by Weakening
    val step3 = have(isO +: inU(x, y, z) :+ (x <= z) :+ (z <= (y u z)) |- x <= (y u z)) subproof :
      have(thesis) by Tautology.from(joinIsClosed of(x := y, y := z), step2) // Cut.withParameters((y u z) ∈ U)(meetIsClosed of(x := y, y := z), step2)
    have(thesis) by Cut.withParameters(z <= (y u z))(step1, step3)
  end rightOr2

  /** STATUS: DONE */
  val commutRL = Theorem(isO +: inU(x, y) :+ (x <= y) |- !y <= !x) :
    have(thesis) by Tautology.from(lemmaForP8)
  end commutRL

  /** STATUS: DONE */
  val commutLL = Theorem(isO +: inU(x, y) :+ (x <= !y) |- y <= !x) :
    val step1 = have(isO +: inU(y) |- y <= !(!y)) subproof :
      assume(isO)
      have(∀(y, (y ∈ U) ==> y <= !(!y))) by Tautology.from(ortholattice.definition, p7a.definition of (x := y))
      val step1 = thenHave((y ∈ U) ==> y <= !(!y)) by InstantiateForall(y)
      assume(y ∈ U)
      have(thesis) by Tautology.from(step1)
    val step2 = have(isO +: inU(x, y) :+ (y <= !(!y)) :+ (!(!y) <= !x) |- y <= !x) subproof :
      val step1 = have(isO +: inU(!x, y) :+ (y <= !(!y)) :+ (!(!y) <= !x) |- y <= !x) by Cut.withParameters(!(!y) ∈ U)(doubleNegationIsClosed of (x := y), cut of (x := y, y := !(!y), z := !x))
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, step1)
    val step3 = have(isO +: inU(x, y) :+ (!(!y) <= !x) |- y <= !x) subproof :
      have(thesis) by Cut.withParameters(y <= !(!y))(step1, step2)
    val step4 = have(isO +: inU(x, y) :+ (x <= !y) |- !(!y) <= !x) subproof :
      have(thesis) by Cut.withParameters(!y ∈ U)(negationIsClosed of (x := y), commutRL of (y := !y))
    have(thesis) by Cut.withParameters(!(!y) <= !x)(step4, step3)
  end commutLL

  /** STATUS: DONE */
  val commutRR = Theorem(isO +: inU(x, y) :+ (!x <= y) |- !y <= x) :
    val step1 = have(isO +: inU(x) |- !(!x) <= x) subproof :
      assume(isO)
      have(∀(x, (x ∈ U) ==> !(!x) <= x)) by Tautology.from(ortholattice.definition, p7b.definition)
      val step1 = thenHave((x ∈ U) ==> !(!x) <= x) by InstantiateForall(x)
      assume(x ∈ U)
      have(thesis) by Tautology.from(step1)
    val step2 = have(isO +: inU(x, y) :+ (!y <= !(!x)) :+ (!(!x) <= x) |- !y <= x) subproof :
      val step1 = have(isO +: inU(x, !y) :+ (!y <= !(!x)) :+ (!(!x) <= x) |- !y <= x) by Cut.withParameters(!(!x) ∈ U)(doubleNegationIsClosed, cut of (x := !y, y := !(!x), z := x))
      have(thesis) by Cut.withParameters(!y ∈ U)(negationIsClosed of (x := y), step1)
    val step3 = have(isO +: inU(x, y) :+ (!y <= !(!x)) |- !y <= x) subproof :
      have(thesis) by Cut.withParameters(!(!x) <= x)(step1, step2)
    val step4 = have(isO +: inU(x, y) :+ (!x <= y) |- !y <= !(!x)) subproof :
      have(thesis) by Cut.withParameters(!x ∈ U)(negationIsClosed, commutRL of (x := !x))
    have(thesis) by Cut.withParameters(!y <= !(!x))(step4, step3)
  end commutRR

  // ==============================================================================================
  // ========================================= TACTICS ============================================
  // ==============================================================================================

  /**
   * Tactic to prove that an element is in an ortholattice
   */
  object ElementInOrtholattice extends ProofTactic:
    private val meet = OrthologicWithAxiomsST.n
    private val join = OrthologicWithAxiomsST.u
    def withParameters(using lib: library.type, proof: lib.Proof)(term: Term)(bot: F.Sequent) : proof.ProofTacticJudgement =
      term match
        case `0` =>
          TacticSubproof:
              have(bot) by Tautology.from(ortholattice.definition, zeroInOrtholattice)
        case `1` =>
          TacticSubproof:
            have(bot) by Tautology.from(ortholattice.definition, oneInOrtholattice)
        case app(`not`, x1) =>
          withParameters(x1)(bot.left |- x1 ∈ U) andThen2 { lastStep =>
            have(bot.left |- !x1 ∈ U) by Cut.withParameters(x1 ∈ U)(lastStep, negationIsClosed of (x := x1))
          }
        case app(`meet`, Pair(left, right)) =>
          withParameters(left)(bot.left |- left ∈ U) andThen { s1 =>
            withParameters(right)(bot.left |- right ∈ U) andThen2 { s2 =>
              have(bot.left |- left ∈ U /\ right ∈ U) by RightAnd(s1, s2)
              have(bot.left |- (left n right) ∈ U) by Cut(lastStep, meetIsClosed of(x := left, y := right))
            }
          }
        case app(`join`, Pair(left, right)) =>
          withParameters(left)(bot.left |- left ∈ U) andThen { s1 =>
            withParameters(right)(bot.left |- right ∈ U) andThen2 { s2 =>
              have(bot.left |- left ∈ U /\ right ∈ U) by RightAnd(s1, s2)
              have(bot.left |- (left u right) ∈ U) by Cut(lastStep, joinIsClosed of(x := left, y := right))
            }
          }
        case x if bot.left contains x ∈ U =>
          TacticSubproof:
            have(x ∈ U |- x ∈ U) by Restate
            have(bot) by Weakening(lastStep)
        case x =>
          proof.InvalidProofTactic(s"Could not prove $x ∈ $U. Make sure that your sequent has the following form : `(ortholattice, $x ∈ $U, ...) |- ...`")
    end withParameters
  end ElementInOrtholattice

  object SimpleInstantiateForallIn extends ProofTactic:

    def apply1(using lib: library.type, proof: lib.Proof)
              (U: F.Variable)(x: F.Variable)
              (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      require(bot.right.size == 1)

      val bot1 = bot.left |- (x ∈ U) ==> bot.right.head

      TacticSubproof:
        val s1 = have(bot1) by InstantiateForall(x)(premise)
        have(bot) by Tautology.from(s1) // AR !!
    // TODO err messages

    end apply1


    def apply(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(xs: F.Variable*)
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      //      xs.foldRight(premise) { case (x, lastStep) =>
      //
      //        val bot1 = ???
      //        apply1(U)(x)(lastStep)
      //
      //      }
      ???

    end apply

  end SimpleInstantiateForallIn

  // IMPROVE with tactic InstantiateForallInU
  object InstantiateForallIn extends ProofTactic:

    def applyM2(using lib: library.type, proof: lib.Proof)
               (U: F.Variable)(xs: F.Variable*)
               (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      ???

    def applyM(using lib: library.type, proof: lib.Proof)
              (U: F.Variable)(xs: F.Variable*)
              (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      val premiseSequent = proof.getSequent(premise)

      if premiseSequent.right.size != 1 then
        proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
      else
        val phi: F.Formula = premiseSequent.right.head

        //        xs.foldLeft(phi) { case (phi1, x) => ??? }
        def rec(acc: proof.ProofTacticJudgement, phi: F.Formula, xs: Seq[F.Variable]): proof.ProofTacticJudgement =
          xs match
            case Seq() =>
              acc andThen2 { lastStep =>
                have(bot) by Tautology.from(premise, lastStep)
              }

            case x +: xs =>
              println(s"x: $x, phi: $phi")
              val xInU: F.Formula = F.AppliedPredicate(`in`, Seq(x, U))
              if !premiseSequent.left.contains(xInU) then
                proof.InvalidProofTactic(s"LHS of premise sequent does not contain ($x ∈ $U).")
              else
                phi match
                  case F.BinderFormula(F.Forall, `x`, phiBody@F.AppliedConnector(F.Implies, Seq(`xInU`, phiBody2))) =>
                    println(s"phiBody2: $phiBody2")
                    val acc1 = acc andThen2 { lastStep =>
                      println(s"lastStep: ${lastStep.asInstanceOf[proof.ProofStep].bot}")
                      val s1 = have(premiseSequent.left |- phiBody) by Tautology.from(premise, lastStep) // AR need premise everywhere ?
                      have(premiseSequent.left |- phiBody2) by Tautology.from(premise, s1)
                    }
                    rec(acc1, phiBody2, xs)
                  case _ => proof.InvalidProofTactic(s"RHS of premise sequent malformed.") // RN

        val i = proof.ValidProofTactic(
          premiseSequent, // Ar ungly
          Seq(K.Restate(premiseSequent.underlying, -1)),
          Seq(premise)
        )
        rec(i, phi, xs)


    // TODO take U as arg ?
    def apply(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(x: F.Variable)
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val prem = proof.getSequent(premise)
      val xInU: F.Formula = F.AppliedPredicate(`in`, Seq(x, U))

      if prem.right.size != 1 then
        proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
      else if !prem.left.contains(xInU) then
        proof.InvalidProofTactic(s"LHS of premise sequent does not contain ($x ∈ $U).")
      else
        val phi: F.Formula = prem.right.head
        phi match
          case F.BinderFormula(F.Forall, `x`, phiBody) =>
            phiBody match
              case F.AppliedConnector(F.Implies, Seq(`xInU`, phiBody2)) =>
                TacticSubproof {
                  val s1 = have(prem.left |- phiBody) by InstantiateForall(phi, x)(premise)
                  //                  println(s"prem: $prem\ns1: ${s1.bot}\nbot: $bot") // RM
                  have(bot) by Tautology.from(premise, s1)
                }

              case _ => proof.InvalidProofTactic(s"RHS of premise sequent malformed.") // RN
          case _ => proof.InvalidProofTactic(s"RHS of premise sequent malformed.") // RN

    //    def apply(using lib: library.type, proof: lib.Proof)
    //             (xs: F.Variable*)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
    //      val prem = proof.getSequent(premise)
    //
    //      if prem.right.size != 1 then
    //        proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
    //      else
    //        val phi: F.Formula = prem.right.head
    //
    ////        val emptyProof = K.SCProof(IndexedSeq(), IndexedSeq(prem))
    ////        val j = proof.ValidProofTactic(bot, Seq(K.Restate(premiseSequentK, -1)), Seq(premise))
    ////        xs.foldLeft()
    //
    //        (xs, phi) match
    //          case (Seq(), phi) =>
    //            if F.isImplyingSequent(phi, bot) then
    //              proof.ValidProofTactic(
    //                bot,
    //                Seq(K.SCSubproof(res._1.withNewSteps(IndexedSeq(K.Weakening(botK, res._1.length - 1))), Seq(-1))),
    //                Seq(premise)
    //              )
    //
    //            ???
    //
    //          case (x1 +: xs, F.BinderFormula(F.Forall, x2, phiBody)) =>
    //
    //            InstantiateForall(phi, x)(premise)(phiBody)

  end InstantiateForallIn


  object Singleton:
    def unapply(t: F.Term): Option[F.Term] = t match
      case unorderedPair(x1, x2) if x1 == x2 => Some(x1)
      case _ => None

  object Pair:
    def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
      case unorderedPair(unorderedPair(x1, y1), Singleton(x2)) if x1 == x2 => Some((x1, y1))
      case _ => None

  object App:
    def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
      case AppliedFunction(`app`, Seq(fun, arg)) => Some((fun, arg))
      case _ => None

  object RestateWithAxioms extends ProofTactic:

    enum Annotated:
      case L(t: F.Term)
      case R(t: F.Term)
      case N
    import Annotated.*

    // AR
    val leq = OrthologicWithAxiomsST.<=
    val meet = OrthologicWithAxiomsST.n
    val join = OrthologicWithAxiomsST.u
    val not0 = OrthologicWithAxiomsST.not // RN

    var log = false

    object Leq:
      def unapply(t: F.Formula): Option[(F.Term, F.Term)] = t match
        case in(Pair(x, y), `leq`) => Some((x, y))
        case _ => None

    object Meet:
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case App(`meet`, Pair(x, y)) => Some((x, y))
        case _ => None

    object Join:
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case App(`join`, Pair(x, y)) => Some((x, y))
        case _ => None

    object Not:
      def unapply(t: F.Term): Option[F.Term] = t match
        case App(`not0`, x) => Some(x)
        case _ => None

    def apply(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =

      // TODO better error messages
      if bot.right.size != 1 then
        proof.InvalidProofTactic("Only support goals of the form ??? |- left <= right")
      else if !(bot.left contains isO) then
        proof.InvalidProofTactic("Only support goals of the form isO +: ... |- left <= right")
      else bot.right.head match
        //        case in(Pair(left, right), `leq`) =>
        case Leq(left, right) => // FIX
          //          val Leq(left, right) = bot.right.head

          val left1 = if left == `1` then N else L(left)
          val right1 = if right == `0` then N else R(right)
          /*
          (left, right) match
            case (`1`, `0`) | (`0`, `1`) => prove(N, N)
            case (`1`, r) => prove(N, R(r))
            case (r, `1`) =>
            case (l, `0`) =>
          */

          val termsInU = bot.left.collect { case in(x1, `U`) => x1 }

          val axioms = bot.left.collect {
            case t @ Leq(_, _) => t // TODO? check inU ?
            //            case Leq(`1`, `0`) => (N, N)
            //            case Leq(`1`, r) => (N, R(r))
            //            case Leq(l, `0`) => (L(l), N)
            //            case Leq(l, r) => (L(l), R(r))
            // AR!
          }
          if log then println(s"axioms: $axioms")

          withParameters(termsInU, axioms)(left1, right1)
        // TODO Weakening if bot.left contains more stuff

        case _ => proof.InvalidProofTactic("Only support goals of the form () |- left <= right")

    end apply

    // IMPROVE such that do not neet to write .apply
    // isOrthollatice(U, <=, n, u, not) |- left <= right
    def withParameters(using lib: library.type, proof: lib.Proof)
                      //                      (termsInU: Set[Term], axioms: Set[(Annotated, Annotated)])
                      (termsInU: Set[Term], axioms: Set[Formula])
                      (left: Annotated, right: Annotated): proof.ProofTacticJudgement =

      val premises = isO +: inU(termsInU.toSeq*)

      val axFormulas: Set[Term] = axioms
        //        .flatMap(Set(_, _)).collect { case L(x) => x case R(x) => x }
        .flatMap { case Leq(l, r) => Set(l, r) }.filterNot(Set(`0`, `1`)) // AR not exhaustive (flatMap)

      val chacheInU = mMap[Term, Any]() // TODO!

      def provedInU(using proof: lib.Proof)(t: Term): Boolean = proveInU(t).isValid

      def proveInU(using proof: lib.Proof)(t: Term): proof.ProofTacticJudgement =
        val p = assume(premises*)
        t match
          case `1` | `0` => ???
          case x1 if termsInU contains x1 =>
            TacticSubproof:
              have(x1 ∈ U) by Weakening(p)

          case Not(x1) =>
            proveInU(x1) andThen2 { lastStep =>
              have(!x1 ∈ U) by Cut(lastStep, negationIsClosed of (x := x1))
            }

          case Meet(x1, y1) =>
            proveInU(x1) andThen { s1 =>
              proveInU(y1) andThen2 { s2 =>
                have(x1 ∈ U /\ y1 ∈ U) by RightAnd(s1, s2)
                have((x1 n y1) ∈ U) by Cut(lastStep, meetIsClosed of(x := x1, y := y1))
              }
            }

          case Join(x1, y1) =>
            proveInU(x1) andThen { s1 =>
              proveInU(y1) andThen2 { s2 =>
                have(x1 ∈ U /\ y1 ∈ U) by RightAnd(s1, s2)
                have((x1 u y1) ∈ U) by Cut(lastStep, joinIsClosed of(x := x1, y := y1))
              }
            }

          case other => proof.InvalidProofTactic(s"Could not prove $other ∈ $U") // RN?

      end proveInU

      extension (a: Annotated)
        def pos1: Term = a match
          case L(t) => t case R(t) => !t case N => `1`
        def pos2: Term = a match
          case L(t) => !t case R(t) => t case N => `0`

      // MV to proveNoC start a vals

      val cache = mMap[(Annotated, Annotated), Any]()

      var ident = 0

      def prove(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement =
        cache.get(gamma, delta) match
          case Some(cachedSamePath: proof.ProofTacticJudgement) =>
            cachedSamePath
          case Some(r) if r.isInstanceOf[proof.InvalidProofTactic] =>
            r.asInstanceOf[proof.ProofTacticJudgement]
          // NOTE works to avoid cycles but doesn't reuse a ValidProofTactic with different path
          case _ =>
            if log then println(" " * ident + s"== starting prove($gamma, $delta)")
            ident += 1

            cache.addOne((gamma, delta), proof.InvalidProofTactic(s"Starting prove($gamma, $delta)"))
            val res: proof.ProofTacticJudgement = proveNoC(gamma, delta)
            res match
              case proof.ValidProofTactic(bot, _, _) =>
                val expected = gamma.pos1 <= delta.pos2
                assert(bot.right.size == 1, s"${bot.right - expected}")
                assert(bot.right.head == expected, s"\n${bot.right.head} \n!= \n$expected \n$gamma $delta")
              case _ =>
            cache.addOne((gamma, delta), res)

            ident -= 1
            if log then println(" " * ident + s"== ending prove($gamma, $delta) with ${res.isValid}")
            res
      end prove

      def proved(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): Boolean = prove(gamma, delta).isValid

      // IMPROVE by
      //  - rm nesting of subproofs
      //  - rm as mush as can premises of the form isInU

      // CHECK ordering importance

      /*
      L(x) delta --> x <= I(delta)
      gamma R(x) --> I(gamma) <= x

      AR assuming never
      N L
      R N
      * */

      extension (s: Sequent) // RM
        def toString2 = "\nleft:" + s.left.map(f => s"\n\t$f") + "\nright:" + s.right.map(f => s"\n\t$f")

      // prove isO /\ ... in universe |- gamma delta
      def proveNoC(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement = TacticSubproof:
        assume(isO +: inU(termsInU.toSeq*) concat axioms *) // RN

        val gammaF = gamma.pos1 // AR use more
        val deltaF = delta.pos2 // AR use more
        val goalRight = gammaF <= deltaF

        (gamma, delta) match

          case (L(x1), R(y1)) if x1 == y1 =>
            have(inU(x1) |- (x1 <= y1)) by Weakening(hyp of (x := x1))

          //            // NOTE code below is for dicharging merged into main tactic
          //            val s1 = have(proveInU(x1))
          //            have(x1 ∈ U |- x1 <= y1) by Weakening(hyp of (x := x1))
          //            andThen(Discharge(s1))
          ////            have(x1 <= y1) by Cut(s1, hyp of (x := x1))

          // Ax
          case _ if axioms contains (gammaF <= deltaF) =>
            have(gammaF <= deltaF) by RewriteTrue

          /** Deconstructing L **/

          // Contraction
          case (L(x1), N) if proved(L(x1), L(x1)) =>
            val s1 = have(prove(L(x1), L(x1)))
            have(s1.bot.left |- x1 <= `0`) by Cut(s1, contraction1 of (x := x1))

          // Weaken
          case (L(x1), delta) if proved(L(x1), N) =>
            val s1 = have(prove(L(x1), N))
            have(s1.bot.left ++ inU(x1, deltaF) |- x1 <= deltaF) by
              Cut.withParameters(x1 <= `0`)(s1, weaken1 of (x := x1, y := deltaF))

          // LeftNot
          case (L(Not(x1)), delta) if proved(R(x1), delta) =>
            have(prove(R(x1), delta))
          //          case (L(Not(x1)), delta) if proved(delta, R(x1)) && false => ??? // RM

          // LeftAnd
          case (L(Meet(x1, y1)), delta) if proved(L(x1), delta) =>
            val s1 = have(prove(L(x1), delta))
            have(s1.bot.left ++ inU(x1, y1, deltaF) |- (x1 n y1) <= deltaF) by Cut(s1, leftAnd1 of (x := x1, y := y1, z := deltaF))
          case (L(Meet(x1, y1)), delta) if proved(L(y1), delta) =>
            val s1 = have(prove(L(y1), delta))
            have(s1.bot.left ++ inU(x1, y1, deltaF) |- (x1 n y1) <= deltaF) by Cut(s1, leftAnd2 of (x := x1, y := y1, z := deltaF))

          // LeftOr
          case (L(Join(x1, y1)), delta) if proved(L(x1), delta) && proved(L(y1), delta) =>
            val s1 = have(prove(L(x1), delta))
            val s2 = have(prove(L(y1), delta))
            have(s1.bot.left ++ s2.bot.left |- (x1 u y1) <= deltaF) by
              Tautology.from(s1, s2, leftOr of (x := x1, y := y1, z := deltaF)) // IMPROVE use Cut

          case (gamma, L(x1)) if proved(L(x1), gamma) =>
            val s1 = have(prove(L(x1), gamma)) // x1 <= gamma.pos2
            gamma match
              case L(y1) => // s1: x1 <= !y1
                have(s1.bot.left ++ inU(x1, y1) |- y1 <= !x1) by Cut(s1, commutLL of (x := x1, y := y1))
              //                have(s1.bot.left ++ inU(!y1) |- y1 <= !x1) by Cut(s1, commutLL of (x := x1, y := y1))
              case R(y1) => // s1: x1 <= y1
                have(s1.bot.left |- !y1 <= !x1) by Cut(s1, commutRL of (x := x1, y := y1))
              case N => // s1: x1 <= 0
                ??? // AR can happen ?

          /** Deconstructing R **/

          // Contraction
          case (N, R(x1)) if proved(R(x1), R(x1)) =>
            val s1 = have(prove(R(x1), R(x1)))
            have(s1.bot.left |- `1` <= x1) by Cut(s1, contraction2 of (x := x1))

          // Weaken
          case (gamma, R(x1)) if proved(N, R(x1)) =>
            val s1 = have(prove(N, R(x1)))
            assert(s1.bot.right.head == `1` <= x1)

            have(s1.bot.left ++ inU(gammaF, x1) |- gammaF <= x1) by
              //              Cut(s1, weaken2 of (x := gammaF, y := x1))
              Cut.withParameters(`1` <= x1)(s1, weaken2 of (x := gammaF, y := x1)) // FIX

          // RightNot
          case (gamma, R(Not(x1))) if proved(gamma, L(x1)) =>
            have(prove(gamma, L(x1)))

          // RightAnd
          case (gamma, R(Meet(x1, y1))) if proved(gamma, R(x1)) && proved(gamma, R(x1)) =>
            val s1 = have(prove(gamma, R(x1)))
            val s2 = have(prove(gamma, R(y1)))
            have(s1.bot.left ++ s2.bot.left |- gammaF <= (x1 n y1)) by
              Tautology.from(s1, s2, rightAnd of(x := gammaF, y := x1, z := y1)) // IMPROVE by using Cut

          // RightOr
          case (gamma, R(Join(x1, y1))) if proved(gamma, R(x1)) =>
            val s1 = have(prove(gamma, R(x1)))
            have(s1.bot.left ++ inU(gammaF, x1, y1) |- gammaF <= (x1 u y1)) by Cut(s1, rightOr1 of (x := gammaF, y := x1, z := y1))
          case (gamma, R(Join(x1, y1))) if proved(gamma, R(y1)) =>
            val s1 = have(prove(gamma, R(y1)))
            have(s1.bot.left ++ inU(gammaF, x1, y1) |- gammaF <= (x1 u y1)) by Cut(s1, rightOr2 of (x := gammaF, y := x1, z := y1))

          case (R(x1), delta) if proved(delta, R(x1)) =>
            val s1 = have(prove(delta, R(x1))) // delta.pos1 <= x1
            delta match
              case L(y1) => // s1: y1 <= x1
                have(s1.bot.left |- !x1 <= !y1) by Cut(s1, commutRL of(x := y1, y := x1))
              case R(y1) => // s1: !y1 <= x1
                val s2 = commutRR of(x := y1, y := x1)
                have(s1.bot.left ++ inU(x1) |- !x1 <= y1) by Cut(s1, s2) // IMRPOVE rm in(x1)
              case N => // s1: 1 <= x1
                ??? // AR can happen ?

          // AxCut IMPROVE perf ! TODO
          case (gamma, delta) if axFormulas.exists(x1 => proved(gamma, R(x1)) && proved(L(x1), delta)) =>
            LazyList.from(axFormulas)
              .map { x1 => (x1, (prove(gamma, R(x1)), prove(L(x1), delta))) }
              //              .collectFirst { case (x1, (s1: proof.ValidProofTactic, s2: proof.ValidProofTactic)) => // FIX
              .collectFirst { case (x1, (s1, s2)) if s1.isValid && s2.isValid =>

                val prem = s1.asInstanceOf[proof.ValidProofTactic].bot.left ++ s2.asInstanceOf[proof.ValidProofTactic].bot.left
                val s3 = have(prem |- (gammaF <= x1) /\ (x1 <= deltaF)) by RightAnd(have(s1), have(s2))
                val s4 = cut of (x := gammaF, y := x1, z := deltaF)
                val goal: Sequent = prem ++ inU(gammaF, x1, deltaF) |- gammaF <= deltaF
                //                Cut.apply(s3, s4)(goal)
                have(goal) by Cut.withParameters((gammaF <= x1) /\ (x1 <= deltaF))(s3, s4)
                //                have(goal) by Cut(s3, s4)

              }.get

          // Ax REVIEW needed !?
          case _ if axioms contains (delta.pos1 <= gamma.pos2) => ???

          case (gamma, delta) => return proof.InvalidProofTactic(s"No rules applied to $gamma, $delta") // RN?

      end proveNoC

      prove(left, right) andThen2 { s0 =>

        val toDischarge = s0.bot.left.collect {
          case in(x1, `U`) if !termsInU.contains(x1) => x1
        }

        if toDischarge.isEmpty then
          have(s0.bot) by Tautology.from(s0) // FIX
        else
          val fs = toDischarge.toSeq.map { xi => have(proveInU(xi)) }
          have(s0.bot) by Tautology.from(s0) // FIX
          andThen(Discharge(fs *))
      }

    end withParameters

  end RestateWithAxioms

  // ==============================================================================================
  // ======================================== TESTS ===============================================
  // ==============================================================================================

  // ================================ CAN IT PROVE THE AXIOMS ? ===================================

  val proveP1 = Theorem((isO, x ∈ U) |- x <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP1

  // TODO: FIX Left-hand side of second premise does not contain φ as claimed.
  /*val proveP2 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= y, y <= z) |- x <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP2*/

  // TODO: FIX No rules applied to L(0), R(x)
  /*val proveP3A = Theorem((isO, x ∈ U) |- 0 <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP3A*/

  // TODO: FIX No rules applied to L(x), R(1)
  /*val proveP3B = Theorem((isO, x ∈ U) |- x <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveP3B*/

  val proveP4A = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP4A

  val proveP4B = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP4B

  val proveP5A = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= y):
    have(thesis) by RestateWithAxioms.apply
  end proveP5A

  val proveP5B = Theorem((isO, x ∈ U, y ∈ U) |- y <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP5B

  val proveP6A = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= y, x <= z) |- x <= (y n z)):
    have(thesis) by RestateWithAxioms.apply
  end proveP6A

  val proveP6B = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= z, y <= z) |- (x u y) <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP6B

  val proveP7A = Theorem((isO, x ∈ U) |- x <= !(!x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP7A

  val proveP7B = Theorem((isO, x ∈ U) |- !(!x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP7B

  // TODO: FIX Left-hand side of second premise does not contain φ as claimed.
  /*val proveP8 = Theorem((isO, x ∈ U, y ∈ U,  x <= y) |- !y <= !x):
    have(thesis) by RestateWithAxioms.apply
  end proveP8*/

  val proveP9A = Theorem((isO, x ∈ U) |- (x n !x) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveP9A

  val proveP9B = Theorem((isO, x ∈ U) |- 1 <= (x u !x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP9B

  // ================================== CAN IT DO REWRITES ? ======================================

  // == ALL SORT OF REWRITES OF P1

  val proveRewriteP1_1 = Theorem((isO, z ∈ U) |- z <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_1

  val proveRewriteP1_2 = Theorem((isO, z ∈ U) |- !z <= !z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_2

  val proveRewriteP1_3 = Theorem((isO, x ∈ U, y ∈ U) |- (x u y) <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_3

  val proveRewriteP1_4 = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= (x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_4

  val proveRewriteP1_5 = Theorem((isO, x ∈ U, y ∈ U) |- !(x u y) <= !(x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_5

  val proveRewriteP1_6 = Theorem((isO, x ∈ U, y ∈ U) |- !(x n y) <= !(x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_6

  // == ALL SORT OF REWRITES OF P2

  // TODO

  // ALL SORT OF REWRITES OF P3A

  // TODO: FIX No rules applied to L(0), R(a)
  /*val proveRewriteP3A_1 = Theorem((isO, a ∈ U) |- 0 <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_1*/

  // TODO: FIX No rules applied to L(0), R(app(not, a))
  /*val proveRewriteP3A_2 = Theorem((isO, a ∈ U) |- 0 <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_2*/

  // TODO: FIX No rules applied to L(0), R(app(u, unorderedPair(unorderedPair(a, b), unorderedPair(a, a))))
  /*val proveRewriteP3A_3 = Theorem((isO, a ∈ U, b ∈ U) |- 0 <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_3*/

  // TODO: FIX No rules applied to L(0), R(app(n, unorderedPair(unorderedPair(a, b), unorderedPair(a, a))))
  /*val proveRewriteP3A_4 = Theorem((isO, a ∈ U, b ∈ U) |- 0 <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_4*/

  // == ALL SORT OF REWRITES OF P3B

  // TODO: FIX No rules applied to L(a), R(1)
  /*val proveRewriteP3B_1 = Theorem((isO, a ∈ U) |- a <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_1*/

  // TODO: FIX No rules applied to L(app(not, a)), R(1)
  /*val proveRewriteP3B_2 = Theorem((isO, a ∈ U) |- !a <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_2*/

  // TODO: FIX No rules applied to L(app(u, unorderedPair(unorderedPair(a, b), unorderedPair(a, a)))), R(1)
  /*val proveRewriteP3B_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_3*/

  // TODO: FIX L(app(n, unorderedPair(unorderedPair(a, b), unorderedPair(a, a)))), R(1)
  /*val proveRewriteP3B_4 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_4*/

  // == ALL SORT OF REWRITES OF P4A

  val proveRewriteP4A_1 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_1

  val proveRewriteP4A_2 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n b) <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_2

  val proveRewriteP4A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a n !b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_3

  val proveRewriteP4A_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) n c) <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_4

  val proveRewriteP4A_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b u c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_5

  val proveRewriteP4A_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_6

  val proveRewriteP4A_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_7

  // == ALL SORT OF REWRITES OF P4B

  val proveRewriteP4B_1 = Theorem((isO, a ∈ U, b ∈ U) |- a <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_1

  val proveRewriteP4B_2 = Theorem((isO, a ∈ U, b ∈ U) |- !a <= (!a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_2

  val proveRewriteP4B_3 = Theorem((isO, a ∈ U, b ∈ U) |- a <= (a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_3

  // TODO: FIX The statement may be incorrect or not provable within propositional logic
  /*val proveRewriteP4B_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a u b) <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_4*/

  val proveRewriteP4B_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- a <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_5

  // TODO: FIX No rules applied to L(a), R(b)
  /*val proveRewriteP4B_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n b) <= ((a n b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_6*/

  val proveRewriteP4B_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- a <= (a u (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_7

  // == ALL SORT OF REWRITES OF P5A

  val proveRewriteP5A_1 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_1

  val proveRewriteP5A_2 = Theorem((isO, a ∈ U, b ∈ U) |- (a n !b) <= !b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_2

  val proveRewriteP5A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n b) <= b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_3

  val proveRewriteP5A_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b u c)) <= (b u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_4

  val proveRewriteP5A_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) n c) <= c):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_5

  val proveRewriteP5A_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= (b n c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_6

  val proveRewriteP5A_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= c):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_7

  // == ALL SORT OF REWRITES OF P5B

  val proveRewriteP5B_1 = Theorem((isO, a ∈ U, b ∈ U) |- b <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_1

  val proveRewriteP5B_2 = Theorem((isO, a ∈ U, b ∈ U) |- !b <= (a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_2

  val proveRewriteP5B_3 = Theorem((isO, a ∈ U, b ∈ U) |- b <= (!a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_3

  // TODO: FIX The statement may be incorrect or not provable within propositional logic
  /*val proveRewriteP5B_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (b u c) <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_4*/

  val proveRewriteP5B_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- c <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_5

  // TODO: FIX No rules applied to L(b), R(c)
  /*val proveRewriteP5B_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (b n c) <= (a u (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_6*/

  val proveRewriteP5B_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- c <= ((a n b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_7

  // == ALL SORT OF REWRITES OF P6A

  // TODO

  // == ALL SORT OF REWRITES OF P6B

  // TODO

  // == ALL SORT OF REWRITES OF P7A

  val proveRewriteP7A_1 = Theorem((isO, a ∈ U) |- a <= !(!a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_1

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP7A_2 = Theorem((isO, a ∈ U) |- !a <= !(!(!a))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_2*/

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP7A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= !(!(a u b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_3*/

  // TODO: FIX No rules applied to L(a), R(b)
  /*val proveRewriteP7A_4 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= !(!(a n b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_4*/

  // == ALL SORT OF REWRITES OF P7B

  val proveRewriteP7B_1 = Theorem((isO, a ∈ U) |- !(!a) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_1

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP7B_2 = Theorem((isO, a ∈ U) |- !(!(!a)) <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_2*/

  val proveRewriteP7B_3 = Theorem((isO, a ∈ U, b ∈ U) |- !(!(a u b)) <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_3

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP7B_4 = Theorem((isO, a ∈ U, b ∈ U) |- !(!(a n b)) <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_4*/

  // == ALL SORT OF REWRITES OF P8

  // TODO: ADD TESTS

  // == ALL SORT OF REWRITES OF P9A

  val proveRewriteP9A_1 = Theorem((isO, a ∈ U) |- (a n !a) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_1

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP9A_2 = Theorem((isO, a ∈ U) |- (!a n !(!a)) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_2*/

  // TODO: FIX Inferred cut pivot is not a singleton set.
  // NOTE: SIMPLIFY DOUBLE NEGATION IN `proveRewriteP9A_2`
  /*val proveRewriteP9A_3 = Theorem((isO, a ∈ U) |- (!a n a) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_3*/

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP9A_4 = Theorem((isO, a ∈ U, b ∈ U) |- ((a u b) n !((a u b))) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_4*/

  // TODO: FIX No rules applied to L(a), R(b)
  /*val proveRewriteP9A_5 = Theorem((isO, a ∈ U, b ∈ U) |- ((a n b) n !((a n b))) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_5*/

  // == ALL SORT OF REWRITES OF P9B

  val proveRewriteP9B_1 = Theorem((isO, a ∈ U) |- 1 <= (a u !a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_1

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP9B_2 = Theorem((isO, a ∈ U) |- 1 <= (!a u !(!a))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_2*/

  // TODO: FIX Inferred cut pivot is not a singleton set.
  // NOTE: SIMPLIFY DOUBLE NEGATION IN `proveRewriteP9B_2`
  /*val proveRewriteP9B_3 = Theorem((isO, a ∈ U) |- 1 <= (!a u a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_3*/

  val proveRewriteP9B_4 = Theorem((isO, a ∈ U, b ∈ U) |- 1 <= ((a u b) u !(a u b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_4

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val proveRewriteP9B_5 = Theorem((isO, a ∈ U, b ∈ U) |- 1 <= ((a n b) u !(a n b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_5*/

  // =================================== NON-TRIVIAL TESTS ========================================

  // == associativity

  // TODO: FIX No rules applied to L(a), R(b)
  /*val meetIsAssociative_1 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= ((a n b) n c)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_1*/

  // TODO: FIX No rules applied to L(a), R(app(n, unorderedPair(unorderedPair(b, c), unorderedPair(b, b))))
  /*val meetIsAssociative_2 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_2*/

  // TODO: FIX The statement may be incorrect or not provable within propositional logic.
  /*val joinIsAssociative_1 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a u (b u c)) <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_1*/

  // TODO: FIX The statement may be incorrect or not provable within propositional logic.
  /*val joinIsAssociative_2 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) u c) <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_2*/

  // == commutativity

  // TODO: FIX No rules applied to L(b), R(a)
  /*val meetIsCommutative = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= (b n a)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsCommutative*/

  // TODO: FIX The statement may be incorrect or not provable within propositional logic.
  /*val joinIsCommutative = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= (b u a)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsCommutative*/

  // == De Morgan's laws

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val DeMorganLaw_1 = Theorem((isO, a ∈ U, b ∈ U) |- !(a u b) <= (!a n !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_1*/

  // TODO: FIX The statement may be incorrect or not provable within propositional logic
  /*val DeMorganLaw_2 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n !b) <= !(a u b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_2*/

  // TODO: FIX No rules applied to L(a), R(b)
  /*val DeMorganLaw_3 = Theorem((isO, a ∈ U, b ∈ U) |- !(a n b) <= (!a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_3*/

  // TODO: FIX Inferred cut pivot is not a singleton set.
  /*val DeMorganLaw_4 = Theorem((isO, a ∈ U, b ∈ U) |- (!a u !b) <= !(a n b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_4*/

  // == idempotency

  // TODO: FIX The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or lack of verification by a proof tactic.
  /*val joinIsIdempotent_1 = Theorem((isO, x ∈ U) |- (x u x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_1*/

  val joinIsIdempotent_2 = Theorem((isO, x ∈ U) |- x <= (x u x)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_2

  val meetIsIdempotent_1 = Theorem((isO, x ∈ U) |- (x n x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_1

  // TODO: FIX The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or lack of verification by a proof tactic.
  /*val meetIsIdempotent_2 = Theorem((isO, x ∈ U) |- x <= (x n x)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_2*/

  // == absorption

  // TODO: FIX The statement may be incorrect or not provable within propositional logic
  /*val absorption_1 = Theorem((isO, x ∈ U, y ∈ U) |- (x u (x n y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_1 */

  // TODO: FIX Left-hand side of second premise does not contain φ as claimed.
  /*val absorption_2 = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x u (x n y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_2*/

  // TODO: FIX Left-hand side of second premise does not contain φ as claimed
  /*val absorption_3 = Theorem((isO, x ∈ U, y ∈ U) |- (x n (x u y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_3*/

  // TODO: FIX The statement may be incorrect or not provable within propositional logic.
  /*val absorption_4 = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x n (x u y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_4*/

  // == from paper

  // TODO: FIX Left-hand side of second premise does not contain φ as claimed.
  /*val fromPaper = Theorem((isO, x ∈ U, y ∈ U, 1 <= (x n (!x u y))) |- 1 <= y) :
    have(thesis) by RestateWithAxioms.apply
  end fromPaper*/

  // == TEST TACTIC : ElementInOrtholattice

  val elemInOrtho1 = Theorem(ortholattice(U, <=, n, u, not, 0, 1) |- 0 ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(0)
  end elemInOrtho1

  val elemInOrtho2 = Theorem(ortholattice(U, <=, n, u, not, 0, 1) |- 1 ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(1)
  end elemInOrtho2

  val elemInOrtho3 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U) |- x ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x)
  end elemInOrtho3

  val elemInOrtho4 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U) |- !x ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x)
  end elemInOrtho4

  val elemInOrtho5 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n y)
  end elemInOrtho5

  val elemInOrtho6 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x u y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x u y)
  end elemInOrtho6

  val elemInOrtho7 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- !(x u y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!(x u y))
  end elemInOrtho7

  val elemInOrtho8 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- !(x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!(x n y))
  end elemInOrtho8

  val elemInOrtho9 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (!x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x n y)
  end elemInOrtho9

  val elemInOrtho10 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n !y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n !y)
  end elemInOrtho10

  val elemInOrtho11 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (!x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x n y)
  end elemInOrtho11

  val elemInOrtho12 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n !y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n !y)
  end elemInOrtho12

  // ==

end OrthologicWithAxiomsST*/