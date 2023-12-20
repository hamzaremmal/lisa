package lisa.ol

import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicByHamza extends lisa.Main {

  // ==============================================================================================
  // ================================= SETUP OF THE LIBRARY =======================================
  // ==============================================================================================

  private val x, y, z = variable
  private val meet = ConstantFunctionLabel.infix(K.Identifier("/\\"), 2); addSymbol(meet)
  private val join = ConstantFunctionLabel.infix(K.Identifier("\\/"), 2); addSymbol(join)
  private val neg2 = ConstantFunctionLabel(K.Identifier("¬"), 1); addSymbol(neg2)
  private val leq = ConstantPredicateLabel.infix(K.Identifier("<="), 2); addSymbol(leq)
  private val zero = Constant("0"); addSymbol(zero)
  private val one = Constant("1"); addSymbol(one)

  // ==============================================================================================
  // ================================= IMPLICIT CONVERSIONS =======================================
  // ==============================================================================================

  given zero2term: Conversion[0, Term] with
    inline def apply(x: 0): Term = zero

  given one2term: Conversion[1, Term] with
    inline def apply(x: 1): Term = one

  extension (left: Term)
    inline def u(right: Term): Term = OrthologicByHamza.join(left, right)
    inline def n(right: Term): Term = OrthologicByHamza.meet(left, right)
    inline def <=(right: Term): Formula = OrthologicByHamza.leq(left, right)
    inline def ====(right: Term): Formula = (left <= right) /\ (right <= left)
    inline def unary_! : Term = OrthologicByHamza.neg2(left)

  // ==============================================================================================
  // ========================================== AXIOMS ============================================
  // ==============================================================================================

  private val V6 = Axiom(x ==== !(!x))
  private val V8 = Axiom(!(x u y) ==== (!x n !y))
  private val V8p = Axiom(!(x n y) ==== (!x u !y))

  private val P1 = Axiom(x <= x) // <= is reflexive
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

  // ==============================================================================================
  // ======================================== LEMMAS ==============================================
  // ==============================================================================================

  private val complementOfZero = Lemma(!0 ==== 1) {

    val step1 = have(!zero <= 1) subproof {
      have(thesis) by Rewrite(P3p of (x := !0))
    }

    val step2 = have(1 <= !zero) subproof {
      val step1 = have(((x n y) <= y) /\ (y <= (x u y))) by RightAnd(P5, P5p)
      val step2 = have(((0 n !zero) <= !zero) /\ (!zero <= (0 u !zero))) by Rewrite(step1 of (x := 0, y := !zero))
      val step3 = have((0 n !zero) <= (0 u !zero)) by Tautology.from(step2, P2 of (x := (0 n !zero), y := !zero, z := (0 u !zero)))
      sorry
    }

    have(thesis) by RightAnd(step1, step2)
  }

  private val complementOfOne = Lemma(!1 ==== 0) {
    sorry
  }

  // ==============================================================================================
  // ====================================== RULE: HYP =============================================
  // ==============================================================================================

  private val HYP = Theorem(x <= x) {
    have(thesis) by Tautology.from(P1)
  }

  // ==============================================================================================
  // ====================================== RULE: CUT =============================================
  // ==============================================================================================

  // xR /\ xL |- ()
  private val CUT_1_1 = Theorem((1 <= x) /\ (x <= 0) |- one <= zero) {
    have(thesis) by Tautology.from(P2 of (x := 1, y := x, z := 0))
  }

  // xR /\ (xL, yL) |- yL
  private val CUT_1_2 = Theorem((1 <= x) /\ (x <= !y) |- (y <= 0)) {
    assume((1 <= x) /\ (x <= !y))
    val step1 = have(!x <= !1) by Tautology.from(P8 of (x := 1, y := x))
    val step2 = have(!1 <= 0) by Tautology.from(complementOfOne)
    val step3 = have((!x <= !1) /\ (!1 <= 0)) by RightAnd(step1, step2)
    val step4 = have(!x <= 0) by Tautology.from(step3, P2 of (x := !x, y := !1, z := 0))
    val step5 = have(!(!y) <= !x) by Tautology.from(P8 of (y := !y))
    val step6 = have(y <= !(!y)) by Tautology.from(P7 of (x := y))
    val step7 = have((y <= !(!y)) /\ (!(!y) <= !x)) by RightAnd(step5, step6)
    val step8 = have(y <= !x) by Tautology.from(step7, P2 of (x := y, y := !(!y), z := !x))
    val step9 = have((y <= !x) /\ (!x <= 0)) by RightAnd(step8, step4)
    have(thesis) by Tautology.from(step9, P2 of (x := y, y := !x, z := 0))
  }

  // xR /\ (xL, yR) |- yR
  private val CUT_1_3 = Theorem((1 <= x) /\ (x <= y) |- 1 <= y) {
    have(thesis) by Tautology.from(P2 of (x := 1, y := x, z := y))
  }

  // (yL, xR) /\ xL |- yL
  private val CUT_2_1 = Theorem((y <= x) /\ (x <= 0) |- y <= 0) {
    have(thesis) by Tautology.from(P2 of (x := y, y := x, z := 0))
  }

  // (yL, xR) /\ (xL, zL) |- (yL, zL)
  private val CUT_2_2 = Theorem((y <= x) /\ (x <= !z) |- y <= !z) {
    have(thesis) by Tautology.from(P2 of (x := y, y := x, z := !z))
  }

  // (yL, xR) /\ (xL, zR) |- (yL, zR)
  private val CUT_2_3 = Theorem((y <= x) /\ (x <= z) |- y <= z) {
    have(thesis) by Tautology.from(P2 of (x := y, y := x))
  }

  // (yR, xR) /\ xL |- yR
  private val CUT_3_1 = Theorem((!y <= x) /\ (x <= 0) |- 1 <= y) {
    assume((!y <= x) /\ (x <= 0))
    val step1 = have(!x <= !(!y)) by Tautology.from(P8 of (x := !y, y := x))
    val step2 = have(!(!y) <= y) by Tautology.from(P7p of (x := y))
    val step3 = have((!x <= !(!y)) /\ (!(!y) <= y)) by RightAnd(step1, step2)
    val step4 = have(!x <= y) by Tautology.from(step3, P2 of (x := !x, y := !(!y), z := y))
    val step5 = have(!0 <= !x) by Tautology.from(P8 of (y := 0))
    val step6 = have((!0 <= !x) /\ (!x <= y)) by RightAnd(step4, step5)
    val step7 = have(!0 <= y) by Tautology.from(step6, P2 of (x := !0, y := !x, z := y))
    val step8 = have(1 <= !0) by Tautology.from(complementOfZero)
    val step9 = have((1 <= !0) /\ (!0 <= y)) by RightAnd(step8, step7)
    have(thesis) by Tautology.from(step9, P2 of (x := 1, y := !0, z := y))
  }

  // (yR, xR) /\ (xL, zL) |- (yR, zL)
  private val CUT_3_2 = Theorem((!x <= y) /\ (z <= !x) |- z <= y) {
    have(thesis) by Tautology.from(P2 of (x := z, y := !x, z := y))
  }

  // (yR, xR) /\ (xL, zR) |- (yR, zR)
  private val CUT_3_3 = Theorem((!y <= x) /\ (x <= z) |- !y <= z) {
    have(thesis) by Tautology.from(P2 of (x := !y, y := x))
  }

  // ==============================================================================================
  // ===================================== RULE: WEAKEN ===========================================
  // ==============================================================================================

  // () |- ()
  private val WEAKEN_1_1 = Theorem(one <= zero |- one <= zero) {
    have(thesis) by Restate
  }

  // () |- xL
  private val WEAKEN_1_2 = Theorem(one <= 0 |- x <= 0) {
    val step1 = have(one <= 0 |- one <= 0) by Restate
    val step2 = have(x <= 1) by Tautology.from(P3p)
    val step3 = have(one <= 0 |- (x <= 1) /\ (one <= 0)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (y := 1, z := 0))
  }

  // () |- xR
  private val WEAKEN_1_3 = Theorem(one <= 0 |- 1 <= x) {
    val step1 = have(one <= 0 |- one <= 0) by Restate
    val step2 = have(0 <= x) by Tautology.from(P3)
    val step3 = have(one <= 0 |- (one <= 0) /\ (0 <= x)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := 1, y := 0, z := x))
  }

  // xL |- xL
  private val WEAKEN_2_1 = Theorem(x <= 0 |- x <= 0) {
    have(thesis) by Restate
  }

  // xL |- xL, yL
  private val WEAKEN_2_2 = Theorem(x <= 0 |- x <= !y) {
    val step1 = have(x <= 0 |- x <= 0) by Restate
    val step2 = have(0 <= !y) by Rewrite(P3 of (x := !y))
    val step3 = have(x <= 0 |- (x <= 0) /\ (0 <= !y)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (y := 0, z := !y))
  }

  // xL |- xL, yR
  private val WEAKEN_2_3 = Theorem(x <= 0 |- x <= y) {
    val step1 = have(x <= 0 |- x <= 0) by Restate
    val step2 = have(0 <= y) by Rewrite(P3 of (x := y))
    val step3 = have(x <= 0 |- (x <= 0) /\ (0 <= y)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (y := 0, z := y))
  }

  // xR |- xR
  private val WEAKEN_3_1 = Theorem(1 <= x |- 1 <= x) {
    have(thesis) by Restate
  }

  // xR |- xR, yL
  private val WEAKEN_3_2 = Theorem(1 <= x |- y <= x) {
    val step1 = have(1 <= x |- 1 <= x) by Restate
    val step2 = have(y <= 1) by Rewrite(P3p of (x := y))
    val step3 = have(1 <= x |- (y <= 1) /\ (1 <= x)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step2, P2 of (x := y, y := 1, z := x))
  }

  // xR |- xR, yR
  private val WEAKEN_3_3 = Theorem(1 <= x |- !x <= y) {
    assume(1 <= x)
    val step1 = have(!x <= !1) by Tautology.from(P8 of (x := 1, y := x))
    val step2 = have(!1 <= 0) by Tautology.from(complementOfOne)
    val step3 = have((!x <= !1) /\ (!1 <= 0)) by RightAnd(step1, step2)
    val step4 = have(!x <= 0) by Tautology.from(step3, P2 of (x := !x, y := !1, z := 0))
    val step5 = have(0 <= y) by Tautology.from(P3 of (x := y))
    val step6 = have((!x <= 0) /\ (0 <= y)) by RightAnd(step4, step5)
    have(thesis) by Tautology.from(step6, P2 of (x := !x, y := 0, z := y))
  }

  // ==============================================================================================
  // ==================================== RULE: LEFT AND ==========================================
  // ==============================================================================================

  // yL, xL |- yL, (x /\ z)L <=> y <= !x |- y <= !(x /\ z)
  private val LEFT_AND_1 = Theorem(x <= !y |- x <= !(y n z)) {
    val step1 = have(!y <= (!y u !z)) by Tautology.from(P4p of (x := !y, y := !z))
    val step2 = have((!y u !z) <= !(y n z)) by Tautology.from(V8p of (x := y, y := z))
    val step3 = have((!y <= (!y u !z)) /\ ((!y u !z) <= !(y n z))) by RightAnd(step1, step2)
    val step4 = have(!y <= !(y n z)) by Tautology.from(step3, P2 of (x := !y, y := (!y u !z), z := !(y n z)))
    val step5 = have(x <= !y |- x <= !y) by Restate
    val step6 = have(x <= !y |- (x <= !y) /\ (!y <= !(y n z))) by RightAnd(step4, step5)
    have(thesis) by Tautology.from(step6, P2 of (y := !y, z := !(y n z)))
  }

  // yR, xL |- yR, (x /\ z)L <=> x <= y |- (x /\ z) <= y
  private val LEFT_AND_2 = Theorem(x <= y |- (x n z) <= y) {
    val step1 = have((x n z) <= x) by Rewrite(P4 of (y := z))
    val step2 = have(x <= y |- x <= y) by Restate
    val step3 = have(x <= y |- ((x n z) <= x) /\ (x <= y)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := (x n z), y := x, z := y))
  }

  // xL |- (x /\ y)L <=> x <= 0 |- (x /\ y) <= 0
  private val LEFT_AND_3 = Theorem(x <= 0 |- (x n y) <= 0) {
    val step1 = have(x <= 0 |- x <= 0) by Restate
    val step2 = have(x <= 0 |- ((x n y) <= x) /\ (x <= 0)) by RightAnd(step1, P4)
    have(thesis) by Tautology.from(step2, P2 of (x := (x n y), y := x, z := 0))
  }

  // ==============================================================================================
  // =================================== RULE: RIGHT AND ==========================================
  // ==============================================================================================

  // TODO : All of these proofs are similar, can we refactor them in one single proof

  // xR /\ yR |- (x /\ y)R
  private val RIGHT_AND_1 = Theorem((1 <= x) /\ (1 <= y) |- (1 <= (x n y))) {
    have(thesis) by Rewrite(P6 of (x := 1, y := x, z := y))
  }

  // (zL, xR) /\ (zL, yR) |- zL, (x /\ y)R
  private val RIGHT_AND_2 = Theorem((z <= x) /\ (z <= y) |- (z <= (x n y))) {
    have(thesis) by Rewrite(P6 of (x := z, y := x, z := y))
  }

  // (zR, xR) /\ (zR, yR) |- zR, (x /\ y)R
  private val RIGHT_AND_3 = Theorem((!z <= x) /\ (!z <= y) |- !z <= (x n y)) {
    have(thesis) by Rewrite(P6 of (x := !z, y := x, z := y))
  }

  // ==============================================================================================
  // ==================================== RULE: LEFT OR ===========================================
  // ==============================================================================================

  // xL /\ yL |- (x \/ y)L
  private val LEFT_OR_1 = Theorem((x <= 0) /\ (y <= 0) |- (x u y) <= 0) {
    have(thesis) by Rewrite(P6p of (z := 0))
  }

  // (zL, xL) /\ (zL, yL) |- zL, (x \/ y)L
  private val LEFT_OR_2 = Theorem((z <= !x) /\ (z <= !y) |- (z <= !(x u y))) {
    assume((z <= !x) /\ (z <= !y))
    val step1 = have(z <= (!x n !y)) by Rewrite(P6 of (x := z, y := !x, z := !y))
    val step2 = have((!x n !y) <= !(x u y)) by Tautology.from(V8)
    val step3 = have((z <= (!x n !y)) /\ ((!x n !y) <= !(x u y))) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := z, y := (!x n !y), z := !(x u y)))
  }

  // (zR, xL) /\ (zR, yL) |- zR, (x \/ y)L
  private val LEFT_OR_3 = Theorem((x <= z) /\ (y <= z) |- (x u y) <= z) {
    have(thesis) by Tautology.from(P6p)
  }

  // ==============================================================================================
  // ==================================== RULE: RIGHT OR ==========================================
  // ==============================================================================================

  // yL, xR |- yL, (x \/ z)R <=> x <= y |- x <= y \/ z
  private val RIGHT_OR_1 = Theorem(x <= y |- x <= (y u z)) {
    val step1 = have(x <= y |- x <= y) by Restate
    val step2 = have(y <= (y u z)) by Tautology.from(P4p of (x := y, y := z))
    val step3 = have(x <= y |- (x <= y) /\ (y <= (y u z))) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (z := (y u z)))
  }

  // yR, xR |- yR, (x \/ z)R <=> !y <= x |- !y <= (x \/ z)
  private val RIGHT_OR_2 = Theorem(!y <= x |- !y <= (x u z)) {
    have(thesis) by Rewrite(RIGHT_OR_1 of (x := !y, y := x))
  }

  // xR |- (x \/ z)R <=> 1 <= x |- 1 <= (x \/ z)
  private val RIGHT_OR_3 = Theorem(1 <= x |- 1 <= (x u z)) {
    have(thesis) by Rewrite(RIGHT_OR_1 of (x := 1, y := x))
  }

  // ==============================================================================================
  // ===================================== RULE: LEFT NOT =========================================
  // ==============================================================================================

  // yL, xR |- yL, (!x)L <=> y <= x |- y <= !(!x)
  private val LEFT_NOT_1 = Theorem(y <= x |- y <= !(!x)) {
    val step1 = have(y <= x |- y <= x) by Restate
    val step2 = have(x <= !(!x)) by Tautology.from(P7)
    val step3 = have(y <= x |- (y <= x) /\ (x <= !(!x))) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := y, y := x, z := !(!x)))
  }

  // yR, xR |- yR, (!x)L <=> !y <= x |- !x <= y
  private val LEFT_NOT_2 = Theorem(!y <= x |- !x <= y) {
    val step1 = have(!y <= x |- !x <= !(!y)) by Tautology.from(P8 of (x := !y, y := x))
    val step2 = have(!(!y) <= y) by Tautology.from(P7p of (x := y))
    val step3 = have(!y <= x |- (!x <= !(!y)) /\ (!(!y) <= y)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := !x, y := !(!y), z := y))
  }

  // xR |- (!x)L <=> 1 <= x |- !x <= 0
  private val LEFT_NOT_3 = Theorem(1 <= x |- !x <= 0) {
    assume(1 <= x)
    val step1 = have(!x <= !1) by Tautology.from(P8 of (x := 1, y := x))
    val step2 = have(!1 <= 0) by Tautology.from(complementOfOne)
    val step3 = have((!x <= !1) /\ (!1 <= 0)) by RightAnd(step1, step2)
    have(thesis) by Tautology.from(step3, P2 of (x := !x, y := !1, z := 0))
  }

  // ==============================================================================================
  // ===================================== RULE: RIGHT NOT ========================================
  // ==============================================================================================

  // yR, xL |- yR, (!x)R <=> x <= y |- !y <= !x
  private val RIGHT_NOT_1 = Theorem(x <= y |- !y <= !x) {
    have(thesis) by Tautology.from(P8)
  }

  // yL, xL |- yL, (!x)R <=> y <= !x |- y <= !x
  private val RIGHT_NOT_2 = Theorem(y <= !x |- y <= !x) {
    have(thesis) by Restate // TODO : NOT MUCH OF A PROGRESS HERE
  }

  // xL |- (!x)R <=> x <= 0 |- 1 <= !x
  private val RIGHT_NOT_3 = Theorem(x <= 0 |- 1 <= !x) {
    assume(x <= 0)
    val step1 = have(!0 <= !x) by Tautology.from(P8 of (y := 0))
    val step2 = have(1 <= !0) by Tautology.from(complementOfZero)
    val step3 = have((1 <= !0) /\ (!0 <= !x)) by RightAnd(step2, step1)
    have(thesis) by Tautology.from(step3, P2 of (x := 1, y := !0, z := !x))
  }

  // NOTE: WE DON'T NEED TO PROOF THE Ax Rule, NOT SURE

  // ==============================================================================================
  // =================================== UTILITY TACTICS ==========================================
  // ==============================================================================================

  object HypTactic extends ProofTactic {

    def solve(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =
      if bot.left.nonEmpty || bot.right.size != 1 then proof.InvalidProofTactic(s"Tactic operates only on sequents of the form `() |- x <= x`")
      else
        TacticSubproof {
          bot.right.head match
            case leq(phi, psi) if phi == psi =>
              have(bot) by Rewrite(HYP of (x := phi))
            case leq(_, _) =>
              proof.InvalidProofTactic(s"Left-hand side of the <= is different from its right-hand side")
            case _ =>
              proof.InvalidProofTactic(s"Tactic operates only on sequents of the form `() |- x <= x`")
        }
  }

  object RightNotTactic extends ProofTactic {

    def solve(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =
      if bot.left.size != 1 || bot.right.size != 1 then proof.InvalidProofTactic(s"Tactic operates only on sequents of the form `Γ,φL |- Γ,(¬φ)R`")
      else
        TacticSubproof {
          bot.left.head match
            case leq(phi, OrthologicByHamza.zero) =>
              have(bot) by Rewrite(RIGHT_NOT_3 of (x := phi))
            case leq(phi, neg2(psi)) =>
              have(bot) by Rewrite(RIGHT_NOT_2 of (y := phi, x := psi))
            case leq(phi, psi) =>
              have(bot) by Rewrite(RIGHT_NOT_1 of (x := phi, y := psi))
            case _ =>
              proof.InvalidProofTactic(s"Tactic operates only on sequents of the form `() |- x <= x`")
        }

  }

  // ==============================================================================================
  // ==================================== CUBIC TIME TACTIC =======================================
  // ==============================================================================================

  // TODO HR : WRITE THE ALGORITHM HERE

  // ==============================================================================================
  // ========================================== EXAMPLE ===========================================
  // ==============================================================================================

  private val example_01 = Theorem(!x <= !x) {
    val step1 = have(x <= x) by Tautology.from(HYP)
    have(thesis) by Tautology.from(step1, RIGHT_NOT_1 of (y := x))
  }

  private val example_02 = Theorem((x n (!x u y)) <= y) {

    val step1 = have(1 <= (!x u y)) subproof {
      val step1 = have((!x u y) <= (!x u y)) by Rewrite(HYP of (x := (!x u y)))
      val step2 = have(((!x u y) n x) <= (!x u y)) by Tautology.from(step1, LEFT_AND_2 of (x := (!x u y), y := (!x u y), z := x))
      sorry
    }

    sorry
  }

}
