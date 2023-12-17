package lisa.maths

import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

import scala.collection.mutable.Map as mMap

object OrthologicWithAxiomsI2 extends lisa.Main:

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

  val L = ConstantFunctionLabel("L", 1)
  val R = ConstantFunctionLabel("R", 1)
  val N = Constant("N")

  val S = ConstantPredicateLabel("S", 2)

  Set(L, R, N, S) foreach addSymbol


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



  extension (t: Term)
    def isL(x: Term): Formula = t === L(x)
    def isR(x: Term): Formula = t === R(x)
    def isN(x: Term): Formula = t === N // REVIEW can rm x ?
    def isF(x: Term): Formula = isL(x) \/ isR(x) \/ isN(x)
  end extension

  def S2(t1: Term, t2: Term) = S(t1, t2) // RM
  def S1(t: Term): Formula = S2(t, N)
  def S0() = S2(N, N)




  /** DERIVATION RULES */

  // ASK how to make implicit
  val areF: Formula = gamma.isF(g) /\ delta.isF(d)

  val hyp = Theorem(S(L(x), R(x))) {
    have(thesis) by Tautology.from(p1, i1 of (y := x))
  }

  val cut = Theorem(areF /\ S(gamma, R(x)) /\ S(L(x), delta) |- areF /\ S(gamma, delta)) {
    assume(areF)
    val a1 = assume(S(gamma, R(x)))
    val a2 = assume(S(L(x), delta))

    val caseL = have(gamma.isL(g) |- S(gamma, delta)) subproof {
      assume(gamma.isL(g))
      have(S(L(g), R(x))) by Substitution.ApplyRules(gamma.isL(g))(a1)
      val s1 = have(g <= x) by Tautology.from(lastStep, i1 of (x := g, y := x))

      val caseL = have(delta.isL(d) |- S(L(g), delta)) subproof {
        assume(delta.isL(d))
        have(S(L(x), L(d))) by Substitution.ApplyRules(delta.isL(d))(a2)
        have(x <= not(d)) by Tautology.from(lastStep, i2 of (y := d))
        have(g <= not(d)) by Tautology.from(s1, lastStep, p2 of (x := g, y := x, z := not(d)))
        have(S(L(g), L(d))) by Tautology.from(s1, lastStep, p2 of (x := g, y := x, z := not(d)))
        sorry
      }
      val caseR = have(delta.isR(d) |- S(L(g), delta)) subproof {
        sorry
      }
      val caseN = have(delta.isN(d) |- S(L(g), delta)) subproof {
        sorry
      }

      have(S(L(g), delta)) by Tautology.from(caseL, caseR, caseN)
      thenHave(thesis) by Substitution.ApplyRules(gamma.isL(g))
    }

    val caseR = have(gamma.isR(g) |- S(gamma, delta)) subproof {
      sorry
    }

    val caseN = have(gamma.isN(g) |- S(gamma, delta)) subproof {
      sorry
    }

    have(thesis) by Tautology.from(caseL, caseR, caseN)
  }

  val weaken = Theorem(areF /\ S1(gamma) |- areF /\ S(gamma, delta)) {
    val a = assume(areF /\ S1(gamma))



    sorry
  }

  val leftAnd = Theorem(areF /\ S(L(x), delta) |- areF /\ S(L(x n y), delta)) {
    assume(areF /\ S(L(x), delta))

//    val s1 = have(x <= z |- (x n y) <= z) by Tautology.from(p4a, p2 of (x := (x n y), y := x))
//
//    val caseL = have(S(L(x), L(z)) |- S(L(x n y), L(z))) by Tautology.from(
//      i2 of (y := z), s1 of (z := not(z)), i2 of (x := (x n y), y := z)
//    )
//    val caseR = have(S(L(x), R(z)) |- S(L(x n y), R(z))) by Tautology.from(
//      i1 of (y := z), s1, i1 of (x := (x n y), y := z)
//    )
//    val caseN = have(S(L(x), N) |- S(L(x n y), N)) by Tautology.from(
//      i4, s1 of (z := zero), i4 of (x := (x n y))
//    )
//
//    have(thesis) by Tautology.from(
//      i7b of (gamma := L(x), x := z),
//      caseL, caseR, caseN,
//      i7b of (gamma := L(x n y), x := z)
//    )
    sorry
  }

  val leftOr = Theorem(areF /\ S(L(x), delta) /\ S(L(y), delta) |- areF /\ S(L(x u y), delta)) {
    val a1 = assume(S(L(x), delta) /\ S(L(y), delta))

    val caseL = have(delta.isL(d) |- S(L(x u y), delta)) subproof {
      assume(delta.isL(d))
      have(S(L(x), L(d)) /\ S(L(y), L(d))) by Substitution.ApplyRules(delta.isL(d))(a1)
      have(S(L(x u y), L(d))) by Tautology.from(
        lastStep,
        i2 of (y := d), i2 of(x := y, y := d),
        p6b of (z := not(d)),
        i2 of(x := (x u y), y := d)
      )
      thenHave(thesis) by Substitution.ApplyRules(delta.isL(d))
    }

    val caseR = have(delta.isR(d) |- S(L(x u y), delta)) subproof {
      sorry
    }

    val caseN = have(delta.isN(d) |- S(L(x u y), delta)) subproof {
      sorry
    }

    have(thesis) by Tautology.from(caseL, caseR, caseN)
  }

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
//                weaken2 of (gamma := gamma1, delta := delta1),
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



end OrthologicWithAxiomsI2
