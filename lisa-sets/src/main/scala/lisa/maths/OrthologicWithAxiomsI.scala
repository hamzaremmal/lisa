package lisa.maths

import collection.mutable.Map as mMap
import lisa.fol.FOL as F
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicWithAxiomsI extends lisa.Main:

  // ortholattice elements
  val x, y, z = variable


  /** ORTHOLATTICE SYMBOLS */

  val <= = ConstantPredicateLabel("<=", 2)

  val u = ConstantFunctionLabel("u", 2)
  val n = ConstantFunctionLabel("n", 2)
  val not = ConstantFunctionLabel("¬", 1)

  val zero = Constant("0")
  val one = Constant("1")

  Set(<=, u, n, not, zero, one) foreach addSymbol

  extension (left: Term) // FIX
//    def <=(right: Term): Formula = OrthologicWithAxioms.<=(left, right)
//    def u(right: Term): Term = OrthologicWithAxioms.u(left, right)
//    def n(right: Term): Term = OrthologicWithAxioms.n(left, right)
    def <=(right: Term): Formula = AppliedPredicate(OrthologicWithAxioms.<=, Seq(left, right))
    def u(right: Term): Term = AppliedFunction(OrthologicWithAxioms.u, Seq(left, right))
    def n(right: Term): Term = AppliedFunction(OrthologicWithAxioms.n, Seq(left, right))

  def not(right: Term): Term = AppliedFunction(OrthologicWithAxioms.not, Seq(right))


  /** ORTHOLATTICE AXIOMS */

  val p1 = Axiom(x <= x)
  val p2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z))
  val p3a = Axiom(zero <= x)
  val p3b = Axiom(x <= one)
  val p4a = Axiom((x n y) <= x)
  val p4b = Axiom(x <= (x u y))
  val p5a = Axiom((x n y) <= y)
  val p5b = Axiom(y <= (x u y))
  val p6a = Axiom((x <= y) /\ (x <= z) ==> (x <= (y n z)))
  val p6b = Axiom((x <= z) /\ (y <= z) ==> ((x u y) <= z))
  val p7a = Axiom(x <= not(not(x)))
  val p7b = Axiom(not(not(x)) <= x)
  val p8 = Axiom((x <= y) ==> (not(y) <= not(x)))
  val p9a = Axiom((x n not(x)) <= zero)
  val p9b = Axiom(one <= (x u not(x)))


  val notEquiv = Theorem((x <= not(y)) <=> (y <= not(x))) {
    val dir1 = have((x <= not(y)) ==> (y <= not(x))) subproof {
      have(thesis) by Tautology.from(
        p8 of (y := not(y)), // (x <= not(y)) ==> (not(not(y)) <= not(x))
        p7a of (x := y), // y <= not(not(y))
        p2 of(x := y, y := not(not(y)), z := not(x))
      )
    }
    have(thesis) by Tautology.from(dir1, dir1 of(x := y, y := x))
  }

  val p8Cons = Theorem((not(y) <= not(x)) ==> (x <= y)) {
    have(thesis) by Tautology.from(
      p8 of(x := not(y), y := not(x)), // not(not(x)) <= not(not(y))
      p7a, // x <= not(not(x))
      p7b of (x := y), // not(not(y)) <= y
      p2 of(y := not(not(x)), z := not(not(y))),
      p2 of(y := not(not(y)), z := y),
    )
  }


  /** ORTHOLOGIC SEQUENT ENCODING */

  val L = ConstantFunctionLabel("L", 1)
  val R = ConstantFunctionLabel("R", 1)
  val N = Constant("N")

  val S = ConstantPredicateLabel("S", 2)

  Set(L, R, N, S) foreach addSymbol


  // annotated formulas
  val f1, f2, f3 = variable
  val gamma, delta = variable

  val i1 = Axiom(S(L(x), R(y)) <=> (x <= y))
  val i2 = Axiom(S(L(x), L(y)) <=> (x <= not(y)))
  val i3 = Axiom(S(R(x), R(y)) <=> (not(x) <= y))
  val i4 = Axiom(S(L(x), N) <=> (x <= zero))
  val i5 = Axiom(S(R(x), N) <=> (one <= x))
  val i6 = Axiom(S(N, N) <=> (one <= zero))

  // ASK ok ?
  val i0 = Axiom(S(gamma, delta) <=> S(delta, gamma))
//  val i7 = Axiom(S(gamma, delta) ==> gamma.isF /\ delta.isF)
  val i7 = Axiom(S(gamma, delta) ==> ∃(x, gamma.isF(x)) /\ ∃(x, delta.isF(x)))


  extension (t: Term)
//    def isL(x: Term): Formula = (t === L(x)) /\ !(t === R(x)) /\ !(t === N)
//    def isR(x: Term): Formula = (t === R(x)) /\ !(t === L(x)) /\ !(t === N)
//    def isN(x: Term): Formula = (t === N) /\ !(t === L(x)) /\ !(t === R(x))
    def isL(x: Term): Formula = t === L(x)
    def isR(x: Term): Formula = t === R(x)
    def isN(x: Term): Formula = t === N // AR (x)
    def isF(x: Term): Formula = isL(x) \/ isR(x) \/ isN(x)
  end extension

  def S2(t1: Term, t2: Term) =
//    t1.isF /\ t2.isF /\ (S(t1, t2) \/ S(t2, t1))
//    t1.isF /\ t2.isF /\ S(t1, t2)
    S(t1, t2)
  def S1(t: Term): Formula = S2(t, N)
  def S0() = S2(N, N)


  // ASK !!
  val onlyL = Axiom(gamma.isL(x) ==> !gamma.isR(x) /\ !gamma.isN(x))
  val onlyR = Axiom(gamma.isR(x) ==> !gamma.isR(x) /\ !gamma.isN(x))
  val onlyN = Axiom(gamma.isN(x) ==> !gamma.isL(x) /\ !gamma.isR(x))


  val S1L = Lemma(S1(L(x)) <=> S2(L(x), R(zero))) {
    have(thesis) by Tautology.from(i1 of (y := zero), i4)
  }
  val S1R = Lemma(S1(R(x)) <=> S2(L(one), R(x))) {
    have(thesis) by Tautology.from(i1 of (x := one, y := x), i5)
  }
  val S0Eq = Lemma(S0() <=> S2(L(one), R(zero))) {
    have(thesis) by Tautology.from(i1 of (x := one, y := zero), i6)
  }

  val p3aS = Lemma(S(L(zero), R(x))) {
    have(thesis) by Tautology.from(p3a, i1 of (x := zero, y := x))
  }
  val p3bS = Lemma(S(L(x), R(one))) {
    have(thesis) by Tautology.from(p3b, i1 of (y := one))
  }

  val deltaCases = Lemma(delta.isF(y) /\
    ((delta.isL(y)) ==> (x <= not(y))) /\
    ((delta.isR(y)) ==> (x <= y)) /\
    ((delta.isN(y)) ==> (x <= zero)) |- S(L(x), delta)
  ) {
    val a1 = assume(delta.isF(y) /\ ((delta.isL(y)) ==> (x <= not(y))) /\ ((delta.isR(y)) ==> (x <= y)) /\ ((delta.isN(y)) ==> (x <= zero)))

    val caseL = have(delta.isL(y) |- S(L(x), delta)) subproof {
      assume(delta.isL(y))
      have(S(L(x), L(y))) by Tautology.from(a1, i2)
      thenHave(thesis) by Substitution.ApplyRules(delta.isL(y))
    }
    val caseR = have(delta.isR(y) |- S(L(x), delta)) subproof {
      assume(delta.isR(y))
      have(S(L(x), R(y))) by Tautology.from(a1, i1)
      thenHave(thesis) by Substitution.ApplyRules(delta === R(y))
    }
    val caseN = have(delta.isN(y) |- S(L(x), delta)) subproof {
      assume(delta.isN(y))
      have(S(L(x), N)) by Tautology.from(a1, i4)
      thenHave(thesis) by Substitution.ApplyRules(delta.isN(y))
    }

    have(thesis) by Tautology.from(caseL, caseR, caseN)
  }

  val deltaCases2 = Theorem(delta.isF(y) |- S(L(x), delta) <=>
    ((delta.isL(y) ==> (x <= not(y))) /\ (delta.isR(y) ==> (x <= y)) /\ (delta.isN(y) ==> (x <= zero)))
  ) {

    val caseL = have(thesis +<< delta.isL(y)) subproof {
      assume(delta.isL(y))
      val s1 = have(!delta.isR(y) /\ !delta.isN(y)) by Tautology.from(onlyL of (gamma := delta, x := y))
      val s2 = have(S(L(x), delta) <=> (x <= not(y))) by Substitution.ApplyRules(delta.isL(y))(i2)
      have(thesis) by Tautology.from(s1, s2)
    }

    val caseR = have(thesis +<< delta.isR(y)) subproof {
      assume(delta.isR(y))
      val s1 = have(!delta.isL(y) /\ !delta.isN(y)) by Tautology.from(onlyR of (gamma := delta, x := y))
      val s2 = have(S(L(x), delta) <=> (x <= y)) by Substitution.ApplyRules(delta.isR(y))(i1)
      have(thesis) by Tautology.from(s1, s2)
    }

    val caseN = have(thesis +<< delta.isN(y)) subproof {
      assume(delta.isN(y))
      val s1 = have(!delta.isL(y) /\ !delta.isR(y)) by Tautology.from(onlyN of (gamma := delta, x := y))
      val s2 = have(S(L(x), delta) <=> (x <= zero)) by Substitution.ApplyRules(delta.isN(y))(i4)
      have(thesis) by Tautology.from(s1, s2)
    }

    have(thesis) by Tautology.from(caseL, caseR, caseN)
  }

  val gammaCases2 = Theorem(gamma.isF(y) |- S(gamma, R(x)) <=>
    ((gamma.isL(y) ==> (y <= x)) /\ (gamma.isR(y) ==> (not(y) <= x)) /\ (gamma.isN(y) ==> (one <= x)))
  ) {
    sorry
  }

//  val allCases = Theorem(gamma.isF(y) /\ delta.isF(y) |- S(gamma, delta) <=> (
//    (gamma.isL(y) ==> (y <= x)) /\
//    (gamma.isR(y) ==> (not(y) <= x)) /\
//    (gamma.isN(y) ==> (one <= x))
//  )) {
//    sorry
//  }


  val lemma1 = Lemma(S2(gamma, R(y)) |-
    ((gamma === L(x)) ==> (x <= y)) /\
      ((gamma === R(x)) ==> (not(x) <= y))
  ) {
    //    have(S2(L(x), R(y)) ==> (x <= y)) by Tautology.from(i1)
    //    thenHave(gamma === L(x) |- S2(gamma, R(y)) ==> (x <= y)) by Substitution.ApplyRules(gamma === L(x))
    //    val s1 = thenHave(S2(gamma, R(y)) |- (gamma === L(x)) ==> (x <= y)) by Restate
    //
    //    have(S2(R(x), R(y)) ==> (not(x) <= y)) by Tautology.from(i3)
    //    thenHave(gamma === R(x) |- S2(gamma, R(y)) ==> (not(x) <= y)) by Substitution.ApplyRules(gamma === R(x))
    //    val s2 = thenHave(S2(gamma, R(y)) |- (gamma === R(x)) ==> (not(x) <= y)) by Restate
    //
    //    have(thesis) by Tautology.from(s1, s2)
    sorry
  }

  val lemma3 = Lemma(S2(L(zero), delta)) {
    sorry
  }

  val lemma4 = Lemma(S2(gamma, R(one))) {
    sorry
  }

  val lemma2 = Lemma(S1(gamma) |-
    ((gamma === L(x)) ==> (x <= zero)) /\
      ((gamma === R(x)) ==> (one <= x))
  ) {
    //    val s1 = have(one <= not(zero)) by Tautology.from(
    //      p3a of (x := not(one)), // zero <= not(one)
    //      notEquiv of (x := zero, y := one)
    //    )
    //    have(thesis) by Tautology.from(
    //      s1,
    //      lemma1 of (y := zero),
    //      p2 of (x := one, y := not(zero), z := x)
    //    )

    //    have(S1(L(x)) ==> (x <= zero)) by Tautology.from(i4)
    //    thenHave(gamma === L(x) |- S1(gamma) ==> (x <= zero)) by Substitution.ApplyRules(gamma === L(x))
    //    val s1 = thenHave(S1(gamma) |- (gamma === L(x)) ==> (x <= zero)) by Restate
    //
    //    have(S1(R(x)) ==> (one <= x)) by Tautology.from(i5)
    //    thenHave(gamma === R(x) |- S1(gamma) ==> (one <= x)) by Substitution.ApplyRules(gamma === R(x))
    //    val s2 = thenHave(S1(gamma) |- (gamma === R(x)) ==> (one <= x)) by Restate
    //
    //    have(thesis) by Tautology.from(s1, s2)
    sorry
  }

  val lemma5 = Lemma(S1(gamma) <=> S2(gamma, R(one))) {
    sorry
  }


  /** DERIVATION RULES */

  val hyp = Theorem(S2(L(x), R(x))) {
    have(thesis) by Tautology.from(p1, i1 of (y := x))
  }

  val cut = Theorem(S(gamma, R(x)) /\ S(L(x), delta) |- S(gamma, delta)) {
    val a1 = assume(S(gamma, R(x)) /\ S(L(x), delta))

    val caseLL = have(gamma.isL(y) /\ delta.isL(z) |- S(gamma, delta)) subproof {
      assume(gamma.isL(y) /\ delta.isL(z))
      have(S(L(y), R(x)) /\ S(L(x), L(z))) by Substitution.ApplyRules(gamma.isL(y), delta.isL(z))(a1)
      have(S(L(y), L(z))) by Tautology.from(lastStep,
        i1 of (x := y, y := x), // y <= x
        i2 of (y := z), // x <= not(z)
        p2 of (x := y, y := x, z := not(z)), // .. => y <= not(z)
        i2 of (x := y, y := z)
      )
      thenHave(thesis) by Substitution.ApplyRules(gamma.isL(y), delta.isL(z))
    }

    val caseLR = have(gamma.isL(y) /\ delta.isR(z) |- S(gamma, delta)) subproof {
      sorry
    }

    val caseRL = have(gamma.isR(y) /\ delta.isL(z) |- S(gamma, delta)) subproof {
      sorry
    }

    val caseRR = have(gamma.isR(y) /\ delta.isR(z) |- S(gamma, delta)) subproof {
      sorry
    }

//    have(gamma.isF(y) /\ delta.isF(z) |- S(gamma, delta)) by Tautology.from(caseLL, caseLR, caseRL, caseRR)


    have(gamma.isF(y) /\ delta.isF(z) |- S(gamma, delta)) subproof {
      assume(gamma.isF(y) /\ delta.isF(z))

      val s1 = have((gamma.isL(y) ==> (y <= x)) /\ (gamma.isR(y) ==> (not(y) <= x)) /\ (gamma.isN(y) ==> (one <= x))) by Tautology.from(gammaCases2)

      val s2 = have((delta.isL(y) ==> (x <= not(y))) /\ (delta.isR(y) ==> (x <= y)) /\ (delta.isN(y) ==> (x <= zero))) by Tautology.from(deltaCases2)


      sorry
    }

//    have(∃(y, gamma.isF(y))) by Tautology.from(
//      a1,
//      i7 of (delta := R(x))
//    )
//    thenHave(gamma.isF(y)) by RightExists

//    have(thesis) by Tautology.from(caseLL, caseLR, caseRL, caseRR)
    sorry
  }

  val weaken = Theorem(S1(gamma) |- S2(gamma, delta)) {
    val a = assume(S1(gamma))

//    have(gamma.isF) by Tautology.from(i7 of (delta := N))
//
//    val caseL = have(gamma === L(x) |- S(gamma, delta)) subproof {
//      assume(gamma === L(x))
//
//      have(S1(L(x))) by Substitution.ApplyRules(gamma === L(x))(a)
//      have(S(L(x), R(zero))) by Tautology.from(lastStep, S1L)
//      have(x <= zero) by Tautology.from(lastStep, i1 of (y := zero))
//
//
//
//      have(S(L(x), delta))
//
//      thenHave(thesis) by Substitution.ApplyRules(gamma === L(x))
//    }

    sorry
  }

  val weaken2 = Corollary((S1(gamma) \/ S1(delta)) |- S2(gamma, delta)) {
    sorry
  }

  val leftAnd = Theorem(S(L(x), delta) |- S(L(x n y), delta)) {
    assume(S(L(x), delta))
    
    val p2And = p2 of (x := (x n y), y := x)

    val s1 = have(x <= not(z) |- (x n y) <= not(z)) by Tautology.from(p4a, p2And of (z := not(z)))
    val s2 = have(x <= z |- (x n y) <= z) by Tautology.from(p4a, p2And)
    val s3 = have(x <= zero |- (x n y) <= zero) by Tautology.from(p4a, p2And of (z := zero))

    have(∃(z, delta.isF(z))) by Tautology.from(i7)
    
    assume(delta.isF(z))
    have(S(L(x), delta) |- S(L(x n y), delta)) by Tautology.from(
      deltaCases2 of (y := z),
      deltaCases2 of (x := (x n y), y := z),
      s1, s2, s3
    )

    sorry
  }

  val leftOr = Theorem(S2(gamma, L(x)) /\ S2(gamma, L(y)) |- S2(gamma, L(x u y))) {
    sorry
  }

  val leftNot = Theorem(S2(gamma, R(x)) |- S(gamma, L(not(x)))) {
    sorry
  }



  /** RULES */


  object RestateWithAxioms extends ProofTactic:

    def apply(using lib: library.type, proof: lib.Proof)
             (axioms: Set[?])
             (bot: F.Sequent): proof.ProofTacticJudgement = ???

    /**
     * Produce proof of () |- left <= right
     */
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (axioms: Set[?])
                      (left: Term, right: Term): proof.ProofTacticJudgement =

      // s of the form S2(L(x), R(y)) ...
      def solve(goal: Term): proof.ProofTacticJudgement =

        val (gamma, delta) = goal match
          case S(gamma, delta) => (gamma, delta)
          case _ => proof.InvalidProofTactic("") // TODO


        ???
      end solve

      ???
    end withParameters

    // proove () |- S(gamma, delta) if can
    private def prove(using lib: library.type, proof: lib.Proof)
                     (gamma1: Term, delta1: Term): proof.ProofTacticJudgement =
      /*
      if bot.left.nonEmpty || bot.right.size != 1 || bot.right then
        proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
      else bot.right.head match
        case S(gamma, delta) => ???

          bot match
            case Sequent(left, right) if left.nonEmpty || right.size != 1 =>
              proof.InvalidProofTactic("") // TODO
            case Sequent(_, right) => ???
      */

//      TacticSubproof: // REVIEW what this does

      def proveWithHyp = TacticSubproof:
        (gamma1, delta1) match
          case (L(x), R(y)) if x == y => have(S(L(x), R(y))) by Tautology.from(hyp)
          case _ => proof.InvalidProofTactic("Hyp can not be applied")

      def proveWithWeaken: proof.ProofTacticJudgement = TacticSubproof:
        if gamma1 == N || delta1 == N then
          proof.InvalidProofTactic("Weaken can only be applied to solve sequents with 2 formulas")
        else
          LazyList(gamma1, delta1)
            .map(prove(_, N))
            .collectFirst { case step if step.isValid =>
              have(S2(gamma1, delta1)) by Tautology.from(
                have(step),
                weaken2 of (gamma := gamma1, delta := delta1),
              )
            } getOrElse { proof.InvalidProofTactic("Weaken can not be applied") }

      def proveWithLeftNot = TacticSubproof:
        (gamma1, delta1) match

          case (L(not(x)), delta1) =>
            val s1 = prove(R(x), delta1)
            if s1.isValid then
              have(S2(L(not(x)), delta1)) by Tautology.from(
                ???
              )

            ???


      def proveWith: Seq[?] = (gamma1, delta1) match
        case _ => ???

      // options for last proof step of the proof
//      val ops: Seq[Seq[proof.ProofStep]] =
      val ops: Seq[Seq[?]] = ???

      ???
    end prove

  end RestateWithAxioms


//  val test1 = Theorem(x <= x) {
//    have(thesis) by RestateWithAxioms.withParameters(Set())(x, x)
//  }
//
//  val test2 = Theorem(x <= (x u y)) {
//    have(thesis) by RestateWithAxioms.withParameters(Set())(x, (x u y))
//  }
//
//  val test3 = Theorem((y n x) <= x) {
//    have(thesis) by RestateWithAxioms.withParameters(Set())((y n x), x)
//  }
//
//  val test4 = Theorem((x n y) <= (y u z)) {
//    have(thesis) by RestateWithAxioms.withParameters(Set())((x n y) <= (y u z))
//  }
//
//  val semiDistributivITY = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
//    have(thesis) by RestateWithAxioms.withParameters(Set())((x u (y n z)), ((x u y) n (x u z)))
//  }



end OrthologicWithAxiomsI
