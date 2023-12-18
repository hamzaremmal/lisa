package lisa.maths

import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

import scala.collection.mutable.Set as mSet
import scala.collection.mutable.Map as mMap

object OrthologicWithAxiomsI2 extends lisa.Main:


  /** ORTHOLATTICE SYMBOLS **/

  // ortholattice elements
  val x, y, z = variable

  val <= = ConstantPredicateLabel("<=", 2)

  val u = ConstantFunctionLabel("u", 2)
  val n = ConstantFunctionLabel("n", 2)
  val not = ConstantFunctionLabel("¬", 1) // RN

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



  /** ORTHOLATTICE AXIOMS **/

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
  val p9a = Axiom((x n not(x)) <= zero) // FIX not used !!!
  val p9b = Axiom(one <= (x u not(x)))


  // REVIEW

  val p3c = Theorem(not(one) <= x) {
    have(not(x) <= one) by Restate.from(p3b of (x := not(x)))
    have(not(one) <= not(not(x))) by Tautology.from(lastStep, p8 of (x := not(x), y := one))
    have(thesis) by Tautology.from(lastStep, p7b, p2 of (x := not(one), y := not(not(x)), z := x))
  }

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

  val notnot = Theorem((x <= not(not(y))) <=> (x <= y)) {
    have(thesis) by Tautology.from(
      p7a of (x := y), p2 of (y := not(not(y)), z := y),
      p7b of (x := y), p2 of (z := not(not(y)))
    )
  }


  /** ORTHOLOGIC SEQUENT ENCODING **/

  // annotated formulas
  val gamma, delta = variable // RN

  val L = ConstantFunctionLabel("L", 1) // Annotate term as formula on left
  val R = ConstantFunctionLabel("R", 1) // Annotate term as formula on right
  val N = Constant("N") // A placeholder for no formula

  val S = ConstantPredicateLabel("S", 2) // OL Sequent of 2 annotated formulas
  val I = ConstantFunctionLabel("I", 1) // interpretation of annotated formula

  Set(L, R, N, S, I) foreach addSymbol


  // RN
  val j4 = Axiom(S(gamma, delta) <=> (I(gamma) <= not(I(delta))))
  val j1 = Axiom(I(L(x)) === x)
  val j2 = Axiom(I(R(x)) === not(x))
  val j3 = Axiom(I(N) === one)


  def S1(t: Term): Formula = S(t, N) \/ S(N, t)

  // prove(L(n(x, ¬(x))), L(x))

  val commutS = Theorem(S(gamma, delta) <=> S(delta, gamma)) {
    have(thesis) by Tautology.from(
      notEquiv of (x := I(gamma), y := I(delta)),
      j4, j4 of (gamma := delta, delta := gamma)
    )
  }

  val SFR = Theorem(S(gamma, R(y)) <=> (I(gamma) <= y)) {
    have(S(gamma, R(y)) <=> (I(gamma) <= not(I(R(y))))) by Tautology.from(j4 of(delta := R(y)))
    thenHave(S(gamma, R(y)) <=> (I(gamma) <= not(not(y)))) by Substitution.ApplyRules(j2 of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := I(gamma)))
  }

  val SLF = Theorem(S(L(x), delta) <=> (x <= not(I(delta)))) {
    have(S(L(x), delta) <=> (I(L(x)) <= not(I(delta)))) by Tautology.from(j4 of(gamma := L(x)))
    thenHave(thesis) by Substitution.ApplyRules(j1)
  }

  // TODO use above ?
  val SLR = Theorem(S(L(x), R(y)) <=> (x <= y)) {
    have(S(L(x), R(y)) <=> (I(L(x)) <= not(I(R(y))))) by Restate.from(j4 of (gamma := L(x), delta := R(y)))
    thenHave(S(L(x), R(y)) <=> (x <= not(not(y)))) by Substitution.ApplyRules(j1, j2 of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot)
  }

  val SLL = Theorem(S(L(x), L(y)) <=> (x <= not(y))) {
    have(thesis) by Substitution.ApplyRules(j1, j1 of (x := y))(j4 of (gamma := L(x), delta := L(y)))
  }

  val SRR = Theorem(S(R(x), R(y)) <=> (not(x) <= y)) {
    have(S(R(x), R(y)) <=> (I(R(x)) <= not(I(R(y))))) by Restate.from(j4 of (gamma := R(x), delta := R(y)))
    thenHave(S(R(x), R(y)) <=> (not(x) <= not(not(y)))) by Substitution.ApplyRules(j2, j2 of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := not(x)))
  }

  val substL = Theorem((S(L(x), delta), S(L(x), R(y)), S(L(y), R(x))) |- S(L(y), delta)) {
    assume(S(L(x), delta) /\ S(L(x), R(y)) /\ S(L(y), R(x)))

    val I1 = not(I(delta))
    have((x <= I1) /\ (x <= y) /\ (y <= x)) by Tautology.from(SLF, SLR, SLR of (x := y, y := x))

    sorry
  }

  val F, G = function[1]

  val subst = Theorem((S(F(x), G(x)), S(L(x), R(y)), S(L(y), R(x))) |- S(F(y), G(y))) {
    assume(S(F(x), G(x)) /\ S(L(x), R(y)) /\ S(L(y), R(x)))

    val s1 = have((x <= y) /\ (y <= x)) by Tautology.from(SLR, SLR of (x := y, y := x))

    have(I(F(x)) <= not(I(G(x)))) by Tautology.from(j4 of (gamma := F(x), delta := G(x)))

    sorry
  }



  /** DERIVATION RULES **/

  val hyp = Theorem(S(L(x), R(x))) {
    have(thesis) by Tautology.from(p1, SLR of (y := x))
  }


  val cut = Theorem((S(gamma, R(x)), S(L(x), delta)) |- S(gamma, delta)) {
    assume(S(gamma, R(x)) /\ S(L(x), delta))
    val s1 = have(I(gamma) <= x) by Tautology.from(SFR of (y := x))
    val s2 = have(x <= not(I(delta))) by Tautology.from(SLF)
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := x, z := not(I(delta))), j4)
  }

  val weaken = Theorem(S1(gamma) |- S(gamma, delta)) {
    assume(S1(gamma))
    have(I(gamma) <= not(I(N))) by Tautology.from(commutS of (delta := N), j4 of (delta := N))
    val s1 = thenHave(I(gamma) <= not(one)) by Substitution.ApplyRules(j3)
    val s2 = have(not(one) <= not(I(delta))) by Tautology.from(p3c of (x := not(I(delta))))
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := not(one), z := not(I(delta))), j4)
  }

  val contraction = Theorem(S(gamma, gamma) |- S(gamma, N)) {
    assume(S(gamma, gamma))
    val G = I(gamma)

    have(G <= not(G)) by Tautology.from(j4 of (delta := gamma))
    have(G <= (G n not(G))) by Tautology.from(lastStep, p1 of (x := G), p6a of (x := G, y := G, z := not(G)))

//    val s1 = have((G n not(G)) <= zero) by Restate.from(p9a of (x := G))
//    val s2 = have(zero <= not(one)) by Restate.from(p3a of (x := not(one))) // AR
//    have(G <= not(one)) by Tautology.from(
//      s1, p2 of (x := G, y := zero, z := not(one)), ???
//    )

    have(G <= zero) by Tautology.from(lastStep, p9a of (x := G), p2 of (x := G, y := (G n not(G)), z := zero))
    have(G <= not(one)) by Tautology.from(lastStep, p3a of (x := not(one)), p2 of (x := G, y := zero, z := not(one)))
    thenHave(I(gamma) <= not(I(N))) by Substitution.ApplyRules(j3)
    have(thesis) by Tautology.from(lastStep, j4 of (delta := N))
  }

  val leftAnd = Theorem(S(L(x), delta) |- S(L(x n y), delta)) {
    have(S(L(x n y), R(x))) by Tautology.from(p4a, SLR of(x := (x n y), y := x))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := L(x n y)))
  }
  val leftAnd2 = Theorem(S(L(y), delta) |- S(L(x n y), delta)) {
    have(S(L(x n y), R(y))) by Tautology.from(p5a, SLR of(x := (x n y)))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := L(x n y), x := y))
  }

  val leftOr = Theorem((S(L(x), delta), S(L(y), delta)) |- S(L(x u y), delta)) {
    assume(S(L(x), delta) /\ S(L(y), delta))
    have((x <= not(I(delta))) /\ (y <= not(I(delta)))) by Tautology.from(SLF, SLF of (x := y))
    have((x u y) <= not(I(delta))) by Tautology.from(lastStep, p6b of (z := not(I(delta))))
    thenHave(I(L(x u y)) <= not(I(delta))) by Substitution.ApplyRules(j1)
    have(thesis) by Tautology.from(lastStep, j4 of (gamma := L(x u y)))
  }

  val leftNot = Theorem(S(gamma, R(x)) |- S(gamma, L(not(x)))) {
    have(S(L(x), L(not(x)))) by Tautology.from(p7a, SLL of (y := not(x)))
    have(thesis) by Tautology.from(lastStep, cut of (delta := L(not(x))))
  }

  val rightAnd = Theorem((S(gamma, R(x)), S(gamma, R(y))) |- S(gamma, R(x n y))) {
    assume(S(gamma, R(x)) /\ S(gamma, R(y)))
    have((I(gamma) <= x) /\ (I(gamma) <= y)) by Tautology.from(SFR of (y := x), SFR)
    have(I(gamma) <= (x n y)) by Tautology.from(lastStep, p6a of (x := I(gamma), y := x, z := y))
    have(thesis) by Tautology.from(lastStep, SFR of (y := (x n y)))
  }

  val rightOr = Theorem(S(gamma, R(x)) |- S(gamma, R(x u y))) {
    have(S(L(x), R(x u y))) by Tautology.from(p4b, SLR of(y := (x u y)))
    have(thesis) by Tautology.from(lastStep, cut of (delta := R(x u y)))
  }

  val rightNot = Theorem(S(L(x), delta) |- S(R(not(x)), delta)) {
    have(S(R(not(x)), R(x))) by Tautology.from(p7b, SRR of (x := not(x), y := x))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := R(not(x))))
  }


  object RestateWithAxioms extends ProofTactic:

//    def apply(using lib: library.type, proof: lib.Proof)
//             (axioms: Set[?])
//             (bot: Sequent): proof.ProofTacticJudgement = ???

    /**
     * Produce proof of () |- left <= right
     */
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (left: Term, right: Term): proof.ProofTacticJudgement = TacticSubproof:

      val s = prove(L(left), R(right))
      if !s.isValid then return proof.InvalidProofTactic("Could not prove")
      else
        have(left <= right) by Tautology.from(
          have(s),
          SLR of (x := left, y := right)
        )

//      prove(L(left), R(right)) andThen {
//        s => {
//          have(left <= right) by Tautology.from(
//            s,
//            SLR of(x := left, y := right)
//          )
//        }
//      }

    end withParameters

    object Hyp extends ProofTactic:

      /** () |- S(L(x), R(x)) */
      def withParameters(using lib: library.type, proof: lib.Proof) // AR if needed
                        (gamma1: Term, delta1: Term): proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (L(x1), R(y)) if x1 == y =>
//            have(S(L(x1), R(y))) by Restate.from(hyp of (x := x1))
            ???
          case _ =>
            return proof.InvalidProofTactic("Hyp can not be applied")

    end Hyp

//    def proveWithHyp(using lib: library.type, proof: lib.Proof)
//                    (gamma1: Term, delta1: Term): proof.ProofTacticJudgement = TacticSubproof:
//      (gamma1, delta1) match
//        case (L(x1), R(y)) if x1 == y =>
//          have(S(L(x1), R(y))) by Restate.from(hyp of (x := x1))
//        case _ =>
//          return proof.InvalidProofTactic("Hyp can not be applied")


//    def proveWithLeftAnd(using lib: library.type, proof: lib.Proof)
//                        (gamma1: Term, delta1: Term): proof.ProofTacticJudgement = TacticSubproof:
//      (gamma1, delta1) match
//        case (L(x1 n y1), delta1) =>
//          val s1 = prove(L(x1), delta1) // TODO other option
//          if !s1.isValid then proof.InvalidProofTactic("LeftAnd can not be applied")
//          else
//            have(S(L(x1 n y1), delta1)) by Tautology.from(
//              have(s1),
//              leftAnd of (x := x1, y := y1, delta := delta1)
//            )
//        case _ =>
//          proof.InvalidProofTactic("LeftAnd can not be applied")

    // TODO? move orElse as extension here

    // IMPROVE
//    val proven, visited = mSet[Term, Term].empty
    val cache = mMap[(Term, Term), Any]()

    // proove () |- S(gamma, delta) if can
    private def prove(using lib: library.type, proof: lib.Proof)
                     (gamma1: Term, delta1: Term): proof.ProofTacticJudgement =

      def proveWithHyp: proof.ProofTacticJudgement = TacticSubproof: // RM SubProof (constant folding the have ~)
        (gamma1, delta1) match
          case (L(x1), R(y)) if x1 == y =>
            have(S(L(x1), R(y))) by Restate.from(hyp of (x := x1))
          case _ =>
            return proof.InvalidProofTactic("Hyp can not be applied")

      def proveWithWeaken: proof.ProofTacticJudgement = // TacticSubproof:
        if gamma1 == N || delta1 == N then
          proof.InvalidProofTactic("Weaken can only be applied to solve sequents with 2 formulas")
        else
          val tmp1 = prove(gamma1, N) orElse prove(delta1, N)
          tmp1 andThen2 { lastStep =>
            have(S(gamma1, delta1)) by Tautology.from(
              lastStep,
              weaken of (gamma := gamma1, delta := delta1),
            )
          }

      def proveWithContraction: proof.ProofTacticJudgement = // TacticSubproof:
        (gamma1, delta1) match
          case (gamm1, N) =>
            prove(gamma1, gamma1) andThen2 { lastStep =>
              have(S(gamma1, N)) by Tautology.from(
                lastStep,
                contraction of (gamma := gamma1),
              )
            }
          case _ => proof.InvalidProofTactic("Contraction can only be applied to solve sequents with 1 formula")

      def proveWithLeftNot: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (gamma1, L(not(x1))) =>
            prove(gamma1, R(x1)) andThen2 { lastStep =>
              have(S(gamma1, L(not(x1)))) by Tautology.from(
                lastStep,
                leftNot of (gamma := gamma1, x := x1),
              )
            }
          case _ => proof.InvalidProofTactic("LeftNot can not be applied")

      def proveWithLeftAnd: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (L(x1 n y1), delta1) =>
            val opt1 = (prove(L(x1), delta1) andThen2 { lastStep =>
              have(S(L(x1 n y1), delta1)) by
                Tautology.from(lastStep, leftAnd of(x := x1, y := y1, delta := delta1))
            })
            val opt2 = (prove(L(y1), delta1) andThen2 { lastStep =>
              have(S(L(x1 n y1), delta1)) by Tautology.from(
                lastStep,
                leftAnd2 of(x := x1, y := y1, delta := delta1),
              )
            })
            opt1 orElse opt2

          case _ => proof.InvalidProofTactic("LeftAnd can not be applied")

      def proveWithLeftOr: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (L(x1 u y1), delta1) =>
            TacticSubproof:
              val s1 = prove(L(x1), delta1)
              val s2 = prove(L(y1), delta1)
              if !s1.isValid || !s2.isValid then
                return proof.InvalidProofTactic("LeftOr can not be applied")
              else
                have(S(L(x1 u y1), delta1)) by Tautology.from(
                  have(s1),
                  have(s2),
                  leftOr of (x := x1, y := y1, delta := delta1)
                )
          case _ => proof.InvalidProofTactic("LeftOr can not be applied")

      def proveWithRightNot: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (R(not(x1)), delta1) =>
            prove(L(x1), delta1) andThen2 { lastStep =>
              have(S(R(not(x1)), delta1)) by Tautology.from(
                lastStep,
                rightNot of (delta := delta1, x := x1),
              )
            }
          case _ => proof.InvalidProofTactic("RightNot can not be applied")

      def proveWithRightAnd: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (gamma1, R(x1 n y1)) =>
            TacticSubproof:
              val s1 = prove(gamma1, R(x1))
              val s2 = prove(gamma1, R(y1))
              if !s1.isValid || !s2.isValid then
                return proof.InvalidProofTactic("RigthAnd can not be applied")
              else
                have(S(gamma1, R(x1 n y1))) by Tautology.from(
                  have(s1),
                  have(s2),
                  leftOr of (x := x1, y := y1, gamma := gamma1)
                )
          case _ => proof.InvalidProofTactic("RigthAnd can not be applied")

      def proveWithRightOr: proof.ProofTacticJudgement =
        (gamma1, delta1) match
          case (gamma1, R(x1 u y1)) =>
            val s1 = prove(gamma1, R(x1)) orElse prove(gamma1, R(y1))
            s1 andThen2 { lastStep =>
              have(S(gamma1, R(x1 u y1))) by Tautology.from(
                lastStep,
                rightOr of(x := x1, y := y1, gamma := gamma1)
              )
            }

          case _ =>
            proof.InvalidProofTactic("LeftAnd can not be applied")

      // IMPROVE
      def proveFlip: proof.ProofTacticJudgement =
        prove(delta1, gamma1) andThen2 { lastStep =>
          have(S(gamma1, delta1)) by Tautology.from(
            lastStep,
            commutS of (gamma := gamma1, delta := delta1)
          )
        }

      val r: proof.ProofTacticJudgement = cache.get(gamma1, delta1) match
//        case Some(vpt: proof.ValidProofTactic) => vpt
//        case Some(ipt: proof.InvalidProofTactic) => ipt
        case Some(r) if !r.asInstanceOf[proof.ProofTacticJudgement].isValid =>
          r.asInstanceOf[proof.ProofTacticJudgement]
          // For Some(valid) do again since is being refused for dependent type reasons

        case _ =>
//          println(s"== starting prove($gamma1, $delta1)")
//          println(s"cache: $cache")
          cache.addOne((gamma1, delta1), proof.InvalidProofTactic(s"Trying to prove($gamma1, $delta1)"))

          val r = proveWithHyp orElse proveWithWeaken orElse proveWithContraction orElse
            proveWithLeftNot orElse proveWithLeftAnd orElse proveWithLeftOr orElse
            proveWithRightNot orElse proveWithRightAnd orElse proveWithRightOr orElse proveFlip

          r match
            case proof.ValidProofTactic(bot, _, _) => println(s"== endded prove($gamma1, $delta1) = $bot")
            case _ => println(s"== endded prove($gamma1, $delta1) = ???")
          cache.addOne((gamma1, delta1), r)
          r


      // TODO add reversed one
      r
/*
//      val p1 = proveWithHyp(gamma1, delta1)
//      println("after proveWithHyp")
//      if p1.isValid then p1
//      else
//        val p2 = proveWithLeftAnd(gamma1, delta1)
//        if p2.isValid then p2
//        else
//          proof.InvalidProofTactic("ohoh")

//      case class Done(p: proof.ProofTacticJudgement)
//      case class Opt(prem: (Term, Term), proofFromPrem: proof.Fact => proof.ProofTacticJudgement)
//
//      val proveWithHypOpt = LazyList(
//        Done(have(S(L(x), R(y))) by Restate.from(hyp))
//      )
//
//      val proveWithWeaken1Opt =
//        if gamma1 == N || delta1 == N then LazyList.empty
//        else LazyList(Opt(
//          prem = (gamma1, N),
//          proofFromPrem = s => {
//            have(S(gamma1, delta1)) by Tautology.from(
//              s,
//              weaken of (gamma := gamma1, delta := delta1)
//            )
//          }
//        ))


      /*
      def proveWithLeftNot =
        (gamma1, delta1) match
          case (gamma1, L(not(x))) =>
            val s1 = prove(gamma1, R(x))
            if s1.isValid then
              have(S(gamma1, L(not(x)))) by Tautology.from(
                have(s1),
                leftNot of (gamma := gamma1)
              )
          case _ => proof.InvalidProofTactic("LeftNot can not be applied on second formula")

      def proveWithLeftNot2 =
        (gamma1, delta1) match
          case (L(not(x)), delta1) =>
            val s1 = prove(R(x), delta1)
            if s1.isValid then
              have(S(L(not(x)), delta1)) by Tautology.from(
                have(s1),
                leftNot of (gamma := gamma1),
                commutS of (gamma := R(x), delta := delta1),
                commutS of (gamma := L(not(x)), delta := delta1),
              )
          case _ => proof.InvalidProofTactic("LeftNot can not be applied on first formula")
      */


//      LazyList(() => proveWithHyp, () => proveWithWeaken, () => proveWithLeftNot, () => proveWithLeftNot2)
////      LazyList(() => proveWithHyp)
//        .map(_())
//        .collectFirst { case p if !p.isInstanceOf[proof.InvalidProofTactic] => p }
//        .getOrElse { proof.InvalidProofTactic("No rule can be applied") }

//      val opts = proveWithHypOpt ++ proveWithWeaken1Opt
//
//      opts.map {
//        case Done(p) => Done(p)
//        case Opt((x, y), pr) => (prove(x, y), pr)
//      }.collectFirst{
//        case Done(p) => p
//        case (s1, s2p) if s1.isValid => s2p(s1)
//      }


//      TacticSubproof:
//        LazyList(proveWithHyp, proveWithWeaken)
//          .collectFirst { case t if t.isValid => t }
//          .getOrElse { proof.InvalidProofTactic("No rule can be applied") }
*/
    end prove

  end RestateWithAxioms


  val test1 = Theorem(x <= x) {
    val s = RestateWithAxioms.withParameters(x, x)
    have(thesis) by Restate.from(have(s))
  }

  val test2a = Theorem((x n (not(x))) <= zero) {
    val s = RestateWithAxioms.withParameters((x n (not(x))), zero)
    have(thesis) by Restate.from(have(s))
  }

  val test2 = Theorem(x <= (x u y)) {
    val s = RestateWithAxioms.withParameters(x, (x u y))
    have(thesis) by Restate.from(have(s))
  }

  val test3 = Theorem((y n x) <= y) {
    val s = RestateWithAxioms.withParameters((y n x), y)
    have(thesis) by Restate.from(have(s))
  }

  val test3b = Theorem((y n x) <= x) {
    val s = RestateWithAxioms.withParameters((y n x), x)
    have(thesis) by Restate.from(have(s))
  }

  val test4 = Theorem((x n y) <= (y u z)) {
    val s = RestateWithAxioms.withParameters((x n y), (y u z))
    have(thesis) by Restate.from(have(s))
  }

//  val semiDistributivity = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
//    val s = RestateWithAxioms.withParameters((x u (y n z)), ((x u y) n (x u z)))
//    have(thesis) by Restate.from(have(s))
//  }



end OrthologicWithAxiomsI2
