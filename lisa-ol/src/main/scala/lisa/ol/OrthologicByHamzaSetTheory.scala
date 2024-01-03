package lisa.ol

import lisa.maths.settheory.SetTheory.*

object OrthologicByHamzaSetTheory extends lisa.Main {

  // ==============================================================================================
  // ========================================= SYMBOLS ============================================
  // ==============================================================================================

  private val S, <=, meet, join, one, zero, not = variable

  private val x, y, z = variable

  // ==============================================================================================
  // =========================================== DSL ==============================================
  // ==============================================================================================

  given zero2term: Conversion[0, Term] with
    override inline def apply(x: 0): Term = zero

  given one2term: Conversion[1, Term] with
    override inline def apply(x: 1): Term = one

  extension (lhs: Term)
    inline def /\(inline rhs: Term): Term = app(meet, pair(lhs, rhs))
    inline def \/(inline rhs: Term): Term = app(join, pair(lhs, rhs))
    inline def <=(inline rhs: Term): Formula = pair(lhs, rhs) ∈ OrthologicByHamzaSetTheory.<=
    inline def unary_! : Term = app(not, lhs)

  // ==============================================================================================
  // ========================================= THEORY =============================================
  // ==============================================================================================

  // TODO HR : Define what an ortholattice is

  lazy val ortholattice = DEF(S, <=, meet, join, zero, one, not) --> {
    relationBetween(<=, S, S) /\
      functionFrom(meet, cartesianProduct(S, S), S) /\
      functionFrom(join, cartesianProduct(S, S), S) /\
      functionFrom(not, S, S) /\
      zero ∈ S /\ one ∈ S /\ P1(S, <=) /\ P2(S, <=) /\
      P3(S, <=, zero) /\ P3p(S, <=, one) /\
      P4(S, <=, join) /\ P4p(S, <=, meet) /\
      P5(S, <=, join) /\ P5p(S, <=, meet)
    // TODO ...
  }

  om.output(s"ortholattice $ortholattice")

  // ==============================================================================================
  // ========================================== AXIOMS ============================================
  // ==============================================================================================

  /*private val P1 = Axiom(x <= x) // <= is reflexive
  private val P2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z)) // <= is transitive
  private val P3 = Axiom(0 <= x) // 0 is the lower bound
  private val P3p = Axiom(x <= 1) // 1 is the higher bound
  private val P4 = Axiom((x n y) <= x)
  private val P4p = Axiom(x <= (x u y))
  private val P5 = Axiom((x n y) <= y)
  private val P5p = Axiom(y <= (x u y))
  private val P6 = Axiom((x <= y) /\ (x <= z) ==> x <= (y n z))
  private val P6p = Axiom((x <= z) /\ (y <= z) ==> (x u y) <= z)
  private val P7 = Axiom(x <= !(!x))
  private val P7p = Axiom(!(!x) <= x)
  private val P8 = Axiom(x <= y ==> !y <= !x)
  private val P9 = Axiom((x n !x) <= 0)
  private val P9p = Axiom(1 <= (x u !x))*/

  lazy val P1 = DEF(S, <=) --> ∀(x, x ∈ S ==> x <= x)
  lazy val P2 = DEF(S, <=) --> ∀(x, ∀(y, ∀(z, (x ∈ S) /\ (y ∈ S) /\ (z ∈ S) ==> ((x <= y) /\ (y <= z) ==> (x <= z)))))
  lazy val P3 = DEF(S, <=, zero) --> ∀(x, (x ∈ S) /\ (0 ∈ S) ==> 0 <= x)
  lazy val P3p = DEF(S, <=, one) --> ∀(x, (x ∈ S) /\ (1 ∈ S) ==> x <= 1)
  lazy val P4 = DEF(S, <=, meet) --> ∀(x, ∀(y, (x ∈ S) /\ (y ∈ S) ==> (x /\ y) <= x))
  lazy val P4p = DEF(S, <=, join) --> ∀(x, ∀(y, (x ∈ S) /\ (y ∈ S) ==> x <= (x \/ y)))
  lazy val P5 = DEF(S, <=, meet) --> ∀(x, ∀(y, (x ∈ S) /\ (y ∈ S) ==> (x /\ y) <= y))
  lazy val P5p = DEF(S, <=, join) --> ∀(x, ∀(y, (x ∈ S) /\ (y ∈ S) ==> y <= (x \/ y)))
  lazy val P6 = ???
  lazy val P6p = ???
  lazy val P7 = DEF(S, <=, not) --> ∀(x, x ∈ S ==> x <= !(!x))
  lazy val P7p = ???
  lazy val P8 = DEF(S, <=, not) --> ∀(x, ∀(x, (x ∈ S) /\ (y ∈ S) ==> (x <= y ==> !y <= !x)))
  lazy val P9 = ???
  lazy val P9p = ???

  // ==============================================================================================
  // ========================================== LEMMAS ============================================
  // ==============================================================================================

  val complementInLattice = Theorem(ortholattice.applySeq(Seq(S, <=, meet, join, zero, one, not)) |- (x ∈ S) ==> (!x ∈ S)) {
    assume(ortholattice.applySeq(Seq(S, <=, meet, join, zero, one, not)))
    val f, a, b, t = variable
    have(thesis) by Tautology.from(ortholattice.definition, functionFrom.definition, elemOfFunctionFrom of (f := not, a := S, b := S, t := x))
  }

  val meetInLattice = Theorem(???) {
    sorry
  }

  val complementOfOne = Theorem(ortholattice.applySeq(Seq(S, <=, meet, join, zero, one, not)) |- (!0 <= 1) /\ (1 <= !0)) {
    assume(ortholattice.applySeq(Seq(S, <=, meet, join, zero, one, not)))

    val lhs = have(!0 <= 1) subproof {
      have(∀(x, (x ∈ S) /\ (1 ∈ S) ==> x <= 1)) by Tautology.from(ortholattice.definition, P3p.definition)
      val step2 = thenHave((x ∈ S) /\ (1 ∈ S) ==> x <= 1) by InstantiateForall(x)
      val step3 = have(!0 ∈ S) by Tautology.from(ortholattice.definition, complementInLattice of (x := 0))
      have(thesis) by Tautology.from(step3, ortholattice.definition, step2 of (x := !0))
    }

    val rhs = have(1 <= !0) subproof {
      sorry
    }

    have(thesis) by RightAnd(lhs, rhs)
  }

  // ==============================================================================================
  // ==================================== PROOF OF THE RULES ======================================
  // ==============================================================================================

  // xR , xL |- ()
  private val CUT_1_1 = Theorem((ortholattice.applySeq(Seq(S, <=, meet, join, zero, one, not)), x ∈ S, 1 <= x, x <= 0) |- one <= 0) {
    sorry
  }

  // TODO HR : WRITE PROOF OF ALL THE RULES

  // TODO HR : Define a Tactic to proof that if
  //        - x in S ==> !x in S
  //        -

}
