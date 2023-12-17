package lisa.maths

import collection.mutable.Map as mMap
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
    val s1 = have((x <= not(y)) ==> (y <= not(x))) by Tautology.from(
      p8 of (y := not(y)), // (x <= not(y)) ==> (not(not(y)) <= not(x))
      p7a of (x := y), // y <= not(not(y))
      p2 of(x := y, y := not(not(y)), z := not(x))
    )
    have(thesis) by Tautology.from(s1, s1 of(x := y, y := x))
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

  val F = ConstantFunctionLabel("F2", 1) // ASK
  val L = ConstantFunctionLabel("L", 1)
  val R = ConstantFunctionLabel("R", 1)
  val N = Constant("N")

  val S = ConstantPredicateLabel("S", 2)

  Set(F, L, R, N, S) foreach addSymbol


  // annotated formulas
  val f1, f2, f3 = variable
  val gamma, delta = variable // RN
  val g, d = variable

  val i1 = Axiom(S(L(x), R(y)) <=> (x <= y))
  val i2 = Axiom(S(L(x), L(y)) <=> (x <= not(y)))
  val i3 = Axiom(S(R(x), R(y)) <=> (not(x) <= y))
  val i4 = Axiom(S(L(x), N) <=> (x <= zero))
  val i5 = Axiom(S(R(x), N) <=> (one <= x))
  val i6 = Axiom(S(N, N) <=> (one <= zero))

  // ASK ok ?
  val i0 = Axiom(S(gamma, delta) <=> S(delta, gamma))
  val i7 = Axiom(S(F(x), delta) <=> S(L(x), delta) \/ S(R(x), delta) \/ S(N, delta))


  val i7b = Lemma(S(gamma, F(x)) <=> S(gamma, L(x)) \/ S(gamma, R(x)) \/ S(gamma, N)) {
    have(thesis) by Tautology.from(
      i0 of (delta := F(x)),
      i7 of (delta := gamma),
      i0 of (delta := L(x)), i0 of (delta := R(x)), i0 of (delta := N)
    )
  }


  extension (t: Term)
    def isL(x: Term): Formula = t === L(x)
    def isR(x: Term): Formula = t === R(x)
    def isN: Formula = t === N
    def isF(x: Term): Formula = isL(x) \/ isR(x) \/ isN(x)

    def isN(x: Term): Formula = isN // RM
  end extension

  def S2(t1: Term, t2: Term) = S(t1, t2) // RM
  def S1(t: Term): Formula = S2(t, N)
  def S0() = S2(N, N)


//  assume(delta.isF(d))
//  assume(gamma.isF(g))


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


  val isFEq = Theorem(gamma.isF(x) /\ S(gamma, delta) |- S(F(x), delta)) {
    val a1 = assume(S(gamma, delta))

    val caseL = have(gamma.isL(x) |- S(L(x), delta)) by Substitution.ApplyRules(gamma.isL(x))(a1)
    val caseR = have(gamma.isR(x) |- S(R(x), delta)) by Substitution.ApplyRules(gamma.isR(x))(a1)
    val caseN = have(gamma.isN |- S(N, delta)) by Substitution.ApplyRules(gamma.isN)(a1)

    have(thesis) by Tautology.from(caseL, caseR, caseN, i7)
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

//      val s1 = have((gamma.isL(y) ==> (y <= x)) /\ (gamma.isR(y) ==> (not(y) <= x)) /\ (gamma.isN(y) ==> (one <= x))) by Tautology.from(gammaCases2)
//
//      val s2 = have((delta.isL(y) ==> (x <= not(y))) /\ (delta.isR(y) ==> (x <= y)) /\ (delta.isN(y) ==> (x <= zero))) by Tautology.from(deltaCases2)


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

  val leftAnd = Theorem(S(L(x), F(z)) |- S(L(x n y), F(z))) {
    val s1 = have(x <= z |- (x n y) <= z) by Tautology.from(p4a, p2 of (x := (x n y), y := x))

    val caseL = have(S(L(x), L(z)) |- S(L(x n y), L(z))) by Tautology.from(
      i2 of (y := z), s1 of (z := not(z)), i2 of (x := (x n y), y := z)
    )
    val caseR = have(S(L(x), R(z)) |- S(L(x n y), R(z))) by Tautology.from(
      i1 of (y := z), s1, i1 of (x := (x n y), y := z)
    )
    val caseN = have(S(L(x), N) |- S(L(x n y), N)) by Tautology.from(
      i4, s1 of (z := zero), i4 of (x := (x n y))
    )

    have(thesis) by Tautology.from(
      i7b of (gamma := L(x), x := z),
      caseL, caseR, caseN,
      i7b of (gamma := L(x n y), x := z)
    )
  }

  val leftOr = Theorem(delta.isF(z) /\ S(L(x), delta) /\ S(L(y), delta) |- S(L(x u y), F(z))) {
    assume(S(L(x), delta) /\ S(L(y), delta))

    val caseL = have(delta.isL(z) /\ S(L(x), L(z)) /\ S(L(y), L(z)) |- S(L(x u y), L(z))) by Tautology.from(
      i2 of (y := z), i2 of (x := y, y := z),
      p6b of (z := not(z)),
      i2 of (x := (x u y), y := z)
    )
//    val caseL = have(delta.isL(z) /\ S(L(x), L(z)) /\ S(L(y), L(z)) |- S(L(x u y), L(z))) by Tautology.from(
//      i2 of (y := z), i2 of (x := y, y := z),
//      p6b of (z := not(z)),
//      i2 of (x := (x u y), y := z)
//    )
//    val caseR = have(S(L(x), R(z)) /\ S(L(y), R(z)) |- S(L(x u y), R(z))) by Tautology.from(
//      i1 of (y := z), i1 of (x := y, y := z),
//      p6b,
//      i1 of (x := (x u y), y := z)
//    )
//    val caseN = have(S(L(x), N) /\ S(L(y), N) |- S(L(x u y), N)) by Tautology.from(
//      i4 of (y := z), i4 of (x := y, y := z),
//      p6b of (z := zero),
//      i4 of (x := (x u y), y := z)
//    )

    have(thesis) by Tautology.from(
      i7b of (gamma := L(x), x := z), i7b of (gamma := L(y), x := z),
//      caseL, caseR, caseN,
      i7b of (gamma := L(x u y), x := z)
    )
  }

  /*val leftOr = Theorem(gamma.isF(z) /\ S(L(x), gamma) /\ S(L(y), gamma) |- S(L(x u y), gamma) {
    assume(S(L(x), gamma) /\ S(L(y), gamma))
//    val caseL = have(S(L(x), L(z)) /\ S(L(y), L(z)) |- S(L(x u y), L(z))) by Tautology.from(
//      i2 of (y := z), i2 of (x := y, y := z),
//      p6b of (z := not(z)),
//      i2 of (x := (x u y), y := z)
//    )
//    val caseR = have(S(L(x), R(z)) /\ S(L(y), R(z)) |- S(L(x u y), R(z))) by Tautology.from(
//      i1 of (y := z), i1 of (x := y, y := z),
//      p6b,
//      i1 of (x := (x u y), y := z)
//    )
//    val caseN = have(S(L(x), N) /\ S(L(y), N) |- S(L(x u y), N)) by Tautology.from(
//      i4 of (y := z), i4 of (x := y, y := z),
//      p6b of (z := zero),
//      i4 of (x := (x u y), y := z)
//    )

    val caseL = have(gamma.isF(z) |- )
      have(S(L(x), L(z)) /\ S(L(y), L(z)) |- S(L(x u y), L(z))) by Tautology.from(
      i2 of (y := z), i2 of(x := y, y := z),
      p6b of (z := not(z)),
      i2 of(x := (x u y), y := z)
    )

    have(thesis) by Tautology.from(
      i7b of (gamma := L(x), x := z), i7b of (gamma := L(y), x := z),
//      caseL, caseR, caseN,
      i7b of (gamma := L(x u y), x := z)
    )
  }*/

  val leftNot = Theorem(S2(gamma, R(x)) |- S(gamma, L(not(x)))) {
    sorry
  }



  /** RULES */


  object RestateWithAxioms extends ProofTactic:

    def apply(using lib: library.type, proof: lib.Proof)
             (axioms: Set[?])
             (bot: Sequent): proof.ProofTacticJudgement = ???

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
