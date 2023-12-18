package lisa.ol

import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicByHamza extends lisa.Main {

  // ==============================================================================================
  // ================================= SETUP OF THE LIBRARY =======================================
  // ==============================================================================================

  private val x, y, z = variable
  private val n, u = function[2]
  private val neg2 = function[1]
  private val leq = predicate[2]
  private val zero, one = variable

  // ==============================================================================================
  // ================================= IMPLICIT CONVERSIONS =======================================
  // ==============================================================================================

  given convZeroToTerm: Conversion[0, Term] with
    def apply(x: 0): Term = zero

  given convOneToTerm: Conversion[1, Term] with
    def apply(x: 1): Term = one

  extension (left: Term)
    def /\(right: Term): Term = OrthologicByHamza.n(left, right)
    def \/(right: Term): Term = OrthologicByHamza.u(left, right)
    def <=(right: Term): Formula = OrthologicByHamza.leq(left, right)

    def ====(right: Term): Formula = (left <= right) /\ (right <= left)

    def unary_! : Term = OrthologicByHamza.neg2(left)

  // ==============================================================================================
  // ========================================== AXIOMS ============================================
  // ==============================================================================================

  private val V6 = Axiom(x ==== !(!x))
  private val V8 = Axiom(!(x \/ y) ==== (!x /\ !y))
  private val V8p = Axiom(!(x /\ y) ==== (!x \/ !y))

  private val P1 = Axiom(x <= x) // <= is reflexive
  private val P2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z)) // <= is transitive
  private val P3 = Axiom(0 <= x) // 0 is the lower bound
  private val P3p = Axiom(x <= 1) // 1 is the higher bound
  private val P4 = Axiom(x /\ y <= x)
  private val P4p = Axiom(x <= x \/ y)
  private val P5 = Axiom(x /\ y <= y)
  private val P5p = Axiom(y <= x \/ y)
  private val P6 = Axiom((x <= y) /\ (x <= z) ==> x <= (y /\ z))
  private val P7 = Axiom(x <= !(!x))
  private val P8 = Axiom(x <= y ==> !y <= !x)
  private val P9 = Axiom((x /\ !x) <= 0)

  // TODO HR : Define the axioms

  // ==============================================================================================
  // ========================================== RULES =============================================
  // ==============================================================================================

  private val HYP = Theorem(x <= x) {
    have(thesis) by Tautology.from(P1)
  }

  private val CUT = Theorem((x <= y) /\ (y <= z) |- x <= z) {
    have(thesis) by Tautology.from(P2)
  }

  private val WEAKEN = Theorem((x <= 0) \/ (1 <= y) |- x <= y) {
    // Show that x <= 0 |- x <= y
    val lhs = have(x <= 0 |- x <= y) subproof {
      val step1 = have(x <= 0 |- x <= 0) by Restate
      val step2 = have(x <= 0 |- (x <= 0) /\ (0 <= y)) by RightAnd(step1, P3 of (x := y))
      have(thesis) by Tautology.from(step2, P2 of (x := x, y := 0, z := y))
    }

    // Show that 1 <= y |- x <= y
    val rhs = have(1 <= y |- x <= y) subproof {
      val step1 = have(1 <= y |- 1 <= y) by Restate
      val step2 = have(1 <= y |- (1 <= y) /\ (x <= 1)) by RightAnd(step1, P3p)
      have(thesis) by Tautology.from(step2, P2 of (x := x, y := 1, z := y))
    }

    have(thesis) by LeftOr(lhs, rhs)
  }

  private val LEFT_AND = Theorem((x <= !y) \/ (y <= 0) |- (x <= !(y /\ z)) \/ ((y /\ z) <= 0)) {

    val lhs = have(x <= !y |- (x <= !(y /\ z)) \/ ((y /\ z) <= 0)) subproof {
      val step1 = have(!y <= (!y \/ !z)) by Tautology.from(P4p of (x := !y, y := !z))
      val step2 = have((!y \/ !z) <= !(y /\ z)) by Tautology.from(V8p of (x := y, y := z))
      val step3 = have((!y <= (!y \/ !z)) /\ ((!y \/ !z) <= !(y /\ z))) by RightAnd(step1, step2)
      val step4 = have(!y <= !(y /\ z)) by Tautology.from(step3, P2 of (x := !y, y := (!y \/ !z), z := !(y /\ z)))
      val step5 = have(x <= !y |- x <= !y) by Restate
      val step6 = have(x <= !y |- (x <= !y) /\ (!y <= !(y /\ z))) by RightAnd(step4, step5)
      have(thesis) by Tautology.from(step6, P2 of (y := !y, z := !(y /\ z)))
    }

    val rhs = have(y <= 0 |- (x <= !(y /\ z)) \/ ((y /\ z) <= 0)) subproof {
      val step1 = have(y <= 0 |- y <= 0) by Restate
      val step2 = have(y <= 0 |- (y /\ z) <= y) by Tautology.from(P4 of (x := y, y := z))
      val step3 = have(y <= 0 |- ((y /\ z) <= y) /\ (y <= 0)) by RightAnd(step1, step2)
      val step4 = have(y <= 0 |- (y /\ z) <= 0) by Tautology.from(step3, P2 of (x := (y /\ z), z := 0))
      have(thesis) by RightOr(step4)
    }

    have(thesis) by LeftOr(lhs, rhs)
  }

  private val RIGHT_AND = Theorem((x <= y) /\ (x <= z) |- x <= (y /\ z)) {
    have(thesis) by Tautology.from(P6)
  }

  private val LEFT_OR = Theorem((x <= !y) /\ (x <= !z) |- x <= !(y \/ z)) {
    val step1 = have((x <= !y) /\ (x <= !z) |- x <= (!y /\ !z)) subproof {
      have(thesis) by Tautology.from(P6 of (y := !y, z := !z))
    }

    val step2 = have(x <= (!y /\ !z) |- x <= !(y \/ z)) subproof {
      val step1 = have((!y /\ !z) <= !(y \/ z)) by Tautology.from(V8 of (x := y, y := z))
      val step2 = have(x <= (!y /\ !z) |- x <= (!y /\ !z)) by Restate
      val step3 = have(x <= (!y /\ !z) |- (x <= (!y /\ !z)) /\ ((!y /\ !z) <= !(y \/ z))) by RightAnd.apply(step1, step2)
      have(thesis) by Tautology.from(step3, P2 of (y := (!y /\ !z), z := !(y \/ z)))
    }

    have(thesis) by Cut.withParameters(x <= (!y /\ !z))(step1, step2)
  }

  private val RIGHT_OR = Theorem(x <= y |- x <= (y \/ z)) {
    sorry
  }

  private val LEFT_NOT = Theorem(x <= y |- x <= !(!y)) {
    val step1 = have(x <= y |- x <= y) by Restate
    val step2 = have(y <= !(!y)) by Tautology.from(V6 of (x := y))
    val step3 = have(x <= y |- (x <= y) /\ (y <= !(!y))) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (z := !(!y)))
  }

  private val RIGHT_NOT = Theorem(x <= !y |- x <= !(!y)) {
    sorry
  }

  // NOTE: WE DON'T NEED TO PROOF THE Ax Rule, NOT SURE

  // ==============================================================================================
  // ========================================= TACTIC =============================================
  // ==============================================================================================

  trait AxiomaticSequentProofTactic {
    def from(using lib: Library, proof: lib.Proof)(axioms: Formula*)(bot: Sequent): proof.ProofTacticJudgement
  }

  object OrthologicWithAxioms extends ProofTactic with AxiomaticSequentProofTactic:
    def from(using lib: Library, proof: lib.Proof)(axioms: Formula*)(bot: Sequent): proof.ProofTacticJudgement =
      Sorry.apply(bot)

  // ==============================================================================================
  // ========================================== EXAMPLE ===========================================
  // ==============================================================================================

  private val example_01 = Theorem((x /\ (!x \/ y)) <= y) {
    have(thesis) by OrthologicWithAxioms.from(((x /\ (!x \/ y))) ==== 1)
  }

}
