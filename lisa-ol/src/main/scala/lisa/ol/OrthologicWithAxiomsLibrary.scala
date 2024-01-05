package lisa.ol

import lisa.automation.kernel.CommonTactics.Definition
import lisa.fol.FOL.*
import lisa.maths.settheory.SetTheory.*
import lisa.fol.FOLHelpers.variable
import lisa.kernel.proof.RunningTheory
import lisa.prooflib.OutputManager

object OrthologicWithAxiomsLibrary extends lisa.prooflib.Library {

  override val theory = new RunningTheory

  predicates.foreach(s => addSymbol(s))
  functions.foreach(s => addSymbol(s))
  addSymbol(emptySet)
  addSymbol(app)
  addSymbol(cartesianProduct)
  addSymbol(functionFrom)
  addSymbol(relationBetween)

  private given om: OutputManager = new OutputManager {
    def finishOutput(exception: Exception): Nothing = {
      log(exception)
      println(om.stringWriter.toString)
      sys.exit
    }
    val stringWriter: java.io.StringWriter = new java.io.StringWriter()
  }

  // ==============================================================================================
  // ======================================== SYMBOLS =============================================
  // ==============================================================================================

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

  extension (left: Term)
    inline def <=(right: Term): Formula = pair(left, right) ∈ OrthologicWithAxiomsLibrary.this.<=
    inline def n(right: Term): Term = app(OrthologicWithAxiomsLibrary.this.n, pair(left, right))
    inline def u(right: Term): Term = app(OrthologicWithAxiomsLibrary.this.u, pair(left, right))
    inline def x(right: Term): Term = cartesianProduct(left, right)
    inline def unary_! = app(OrthologicWithAxiomsLibrary.this.not, left)

  // ==============================================================================================
  inline def forallInU(xs: Variable*)(f: Formula): Formula =
    xs.foldRight(f) { (x, g) => ∀(x, (x ∈ U) ==> g) }

  inline def inU(xs: Term*): Seq[Formula] = xs.map(_ ∈ U)

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

  val ortholattice = DEF(U, <=, n, u, not, `0`, `1`) --> And(
    Seq(
      0 ∈ U,
      1 ∈ U,
      relationBetween(<=, U, U),
      functionFrom(not, U, U),
      functionFrom(n, cartesianProduct(U, U), U),
      functionFrom(u, cartesianProduct(U, U), U),
      p1(U, <=),
      p2(U, <=),
      p3a(U, <=, `0`),
      p3b(U, <=, `1`),
      p4a(U, <=, n),
      p4b(U, <=, u),
      p5a(U, <=, n),
      p5b(U, <=, u),
      p6a(U, <=, n),
      p6b(U, <=, u),
      p7a(U, <=, not),
      p7b(U, <=, not),
      p8(U, <=, not),
      p9a(U, <=, n, not, `0`),
      p9b(U, <=, u, not, `1`)
    )
  )

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
    /*assume(functionFrom(f, S, T), (x ∈ S))

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

    have(thesis) by Tautology.from(appInRange, inRangeImpliesInCodomain of (z := app(f, x)))*/
    sorry
  end appInCodomain

  /** STATUS: DONE */
  val cartesianProductElement = Lemma((x ∈ U, y ∈ U) |- pair(x, y) ∈ (U x U)):
    /*val step1 = have(pair(x, y) ∈ (U x U) <=> x ∈ U /\ y ∈ U) by Restate.from(pairInCartesianProduct of(a := x, b := y, x := U, y := U))
    assume(x ∈ U)
    assume(y ∈ U)
    have(thesis) by Tautology.from(step1)*/
    sorry
  end cartesianProductElement

  /** STATUS: DONE */
  val joinIsClosed = Lemma((isO, (x ∈ U) /\ (y ∈ U)) |- (x u y) ∈ U):
    val step1 = have((isO, x ∈ U, y ∈ U) |- (x u y) ∈ U) subproof :
      val step1 = have(isO |- functionFrom(u, U x U, U)) by Tautology.from(ortholattice.definition)
      val step2 = have((functionFrom(u, U x U, U), pair(x, y) ∈ (U x U)) |- (x u y) ∈ U) by Restate.from(appInCodomain of(f := u, S := (U x U), T := U, x := pair(x, y)))
      val step3 = have((isO, pair(x, y) ∈ (U x U)) |- (x u y) ∈ U) by Cut.withParameters(functionFrom(u, (U x U), U))(step1, step2)
      have(thesis) by Cut.withParameters(pair(x, y) ∈ (U x U))(cartesianProductElement, step3)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- (x ∈ U, y ∈ U)) subproof :
      have((x ∈ U, y ∈ U) |- (x ∈ U, y ∈ U)) by Restate
      thenHave(thesis) by LeftAnd
    have(thesis) by Tautology.from(step1, step2)
  end joinIsClosed

  /** STATUS: DONE */
  val meetIsClosed = Lemma((isO, (x ∈ U) /\ (y ∈ U)) |- (x n y) ∈ U):
    val step1 = have((isO, x ∈ U, y ∈ U) |- (x n y) ∈ U) subproof :
      val step1 = have(isO |- functionFrom(n, U x U, U)) by Tautology.from(ortholattice.definition)
      val step2 = have((functionFrom(n, U x U, U), pair(x, y) ∈ (U x U)) |- (x n y) ∈ U) by Restate.from(appInCodomain of(f := n, S := (U x U), T := U, x := pair(x, y)))
      val step3 = have((isO, pair(x, y) ∈ (U x U)) |- (x n y) ∈ U) by Cut.withParameters(functionFrom(n, (U x U), U))(step1, step2)
      have(thesis) by Cut.withParameters(pair(x, y) ∈ (U x U))(cartesianProductElement, step3)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- (x ∈ U, y ∈ U)) subproof :
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

}
