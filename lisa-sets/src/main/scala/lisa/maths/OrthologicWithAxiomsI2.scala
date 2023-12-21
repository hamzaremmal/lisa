package lisa.maths

import lisa.fol.FOL
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.*

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
//    def <=(right: Term): Formula = OrthologicWithAxiomsI2.<=(left, right)
//    def u(right: Term): Term = OrthologicWithAxiomsI2.u(left, right)
//    def n(right: Term): Term = OrthologicWithAxiomsI2.n(left, right)
    def <=(right: Term): Formula = AppliedPredicate(OrthologicWithAxiomsI2.<=, Seq(left, right))
    def u(right: Term): Term = AppliedFunction(OrthologicWithAxiomsI2.u, Seq(left, right))
    def n(right: Term): Term = AppliedFunction(OrthologicWithAxiomsI2.n, Seq(left, right))



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
  val p9a = Axiom((x n not(x)) <= zero)
  val p9b = Axiom(one <= (x u not(x))) // FIX not used !


  // REVIEW

  // x <= 0 ==> x <= y

  val p3c = Theorem(not(one) <= x) {
    have(not(x) <= one) by Restate.from(p3b of (x := not(x)))
    have(not(one) <= not(not(x))) by Tautology.from(lastStep, p8 of (x := not(x), y := one))
    have(thesis) by Tautology.from(lastStep, p7b, p2 of (x := not(one), y := not(not(x)), z := x))
  }


  val notnot = Theorem((x <= not(not(y))) <=> (x <= y)) {
    val s1 = have((x <= not(not(y))) ==> (x <= y)) by Tautology.from(p7b of (x := y), p2 of (y := not(not(y)), z := y))
    val s2 = have((x <= y) ==> (x <= not(not(y)))) by Tautology.from(p7a of (x := y), p2 of (z := not(not(y))))
    have(thesis) by Tautology.from(s1, s2)
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


  def S1(t: Term): Formula = S(t, N) \/ S(N, t)
  // IMPROVE use more
  def NI(t: Term): Term = not(I(t))


  // RN
  val IS = Axiom(S(gamma, delta) <=> (I(gamma) <= NI(delta)))
  val IL = Axiom(I(L(x)) === x)
  val IR = Axiom(I(R(x)) === not(x))
  val IN = Axiom(I(N) === one)


  val commutS = Theorem(S(gamma, delta) <=> S(delta, gamma)) {
    val impl = have(S(gamma, delta) ==> S(delta, gamma)) subproof {
      assume(S(gamma, delta))
      val (g, d) = (I(gamma), I(delta))
      have(g <= not(d)) by Tautology.from(IS)
      val s1 = have(not(not(d)) <= not(g)) by Tautology.from(lastStep, p8 of (x := g, y := not(d)))
      val s2 = have(d <= not(not(d))) by Tautology.from(p7a of (x := d))
      have(d <= not(g)) by Tautology.from(s1, s2, p2 of (x := d, y := not(not(d)), z := not(g)))
      have(thesis) by Tautology.from(lastStep, IS of (gamma := delta, delta := gamma))
    }
    have(thesis) by Tautology.from(impl, impl of (gamma := delta, delta := gamma))
  }

  val SFR = Theorem(S(gamma, R(y)) <=> (I(gamma) <= y)) {
    have(S(gamma, R(y)) <=> (I(gamma) <= not(I(R(y))))) by Tautology.from(IS of(delta := R(y)))
    thenHave(S(gamma, R(y)) <=> (I(gamma) <= not(not(y)))) by Substitution.ApplyRules(IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := I(gamma)))
  }

  val SLF = Theorem(S(L(x), delta) <=> (x <= NI(delta))) {
    have(S(L(x), delta) <=> (I(L(x)) <= NI(delta))) by Tautology.from(IS of(gamma := L(x)))
    thenHave(thesis) by Substitution.ApplyRules(IL)
  }

  val SLR = Theorem(S(L(x), R(y)) <=> (x <= y)) {
    have(S(L(x), R(y)) <=> (I(L(x)) <= NI(R(y)))) by Restate.from(IS of (gamma := L(x), delta := R(y)))
    thenHave(S(L(x), R(y)) <=> (x <= not(not(y)))) by Substitution.ApplyRules(IL, IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot)
  }

  val SLL = Theorem(S(L(x), L(y)) <=> (x <= not(y))) {
    have(S(L(x), L(y)) <=> (I(L(x)) <= NI(L(y)))) by Restate.from(IS of (gamma := L(x), delta := L(y)))
    thenHave(thesis) by Substitution.ApplyRules(IL, IL of (x := y))
  }

  val SRR = Theorem(S(R(x), R(y)) <=> (not(x) <= y)) {
    have(S(R(x), R(y)) <=> (I(R(x)) <= NI(R(y)))) by Restate.from(IS of (gamma := R(x), delta := R(y)))
    thenHave(S(R(x), R(y)) <=> (not(x) <= not(not(y)))) by Substitution.ApplyRules(IR, IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := not(x)))
  }

  val SLN = Theorem(S(L(x), N) <=> (x <= zero)) {
    have(S(L(x), N) <=> (x <= NI(N))) by Restate.from(SLF of (delta := N))
    thenHave(S(L(x), N) <=> (x <= not(one))) by Substitution.ApplyRules(IN)
    have(thesis) by Tautology.from(lastStep,
      p3c of (x := zero), p2 of (y := not(one), z := zero),
      p3a of (x := not(one)), p2 of (y := zero, z := not(one)),
    )
  }

  val SNR = Theorem(S(N, R(y)) <=> (one <= y)) {
    have(S(N, R(y)) <=> (I(N) <= y)) by Restate.from(SFR of (gamma := N))
    thenHave(thesis) by Substitution.ApplyRules(IN)
  }

  val SNN = Theorem(S(N, N) <=> (one <= zero)) {
    val s1 = have((one <= not(one)) ==> (one <= zero)) by
      Tautology.from(p3c of (x := zero), p2 of (x := one, y := not(one), z := zero))
    val s2 = have((one <= zero) ==> (one <= not(one))) by
      Tautology.from(p3a of (x := not(one)), p2 of (x := one, y := zero, z := not(one)))
    have(S(N, N) <=> (one <= not(one))) by Substitution.ApplyRules(IN)(IS of (gamma := N, delta := N))
    have(thesis) by Tautology.from(lastStep, s1, s2)
  }


  /** DERIVATION RULES **/

  val hyp = Theorem(S(L(x), R(x))) {
    have(thesis) by Tautology.from(p1, SLR of (y := x))
  }

  val cut = Theorem((S(gamma, R(x)), S(L(x), delta)) |- S(gamma, delta)) {
    assume(S(gamma, R(x)) /\ S(L(x), delta))
    val s1 = have(I(gamma) <= x) by Tautology.from(SFR of (y := x))
    val s2 = have(x <= NI(delta)) by Tautology.from(SLF)
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := x, z := NI(delta)), IS)
  }

  val weaken = Theorem(S1(gamma) |- S(gamma, delta)) {
    assume(S1(gamma))
    have(I(gamma) <= NI(N)) by Tautology.from(commutS of (delta := N), IS of (delta := N))
    val s1 = thenHave(I(gamma) <= not(one)) by Substitution.ApplyRules(IN)
    val s2 = have(not(one) <= NI(delta)) by Tautology.from(p3c of (x := NI(delta)))
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := not(one), z := NI(delta)), IS)
  }

  val contraction = Theorem(S(gamma, gamma) |- S(gamma, N)) {
    assume(S(gamma, gamma))
    val G = I(gamma)

    have(G <= not(G)) by Tautology.from(IS of (delta := gamma))
    have(G <= (G n not(G))) by Tautology.from(lastStep, p1 of (x := G), p6a of (x := G, y := G, z := not(G)))

//    val s1 = have((G n not(G)) <= zero) by Restate.from(p9a of (x := G))
//    val s2 = have(zero <= not(one)) by Restate.from(p3a of (x := not(one))) // AR
//    have(G <= not(one)) by Tautology.from(
//      s1, p2 of (x := G, y := zero, z := not(one)), ???
//    )

    have(G <= zero) by Tautology.from(lastStep, p9a of (x := G), p2 of (x := G, y := (G n not(G)), z := zero))
    have(G <= not(one)) by Tautology.from(lastStep, p3a of (x := not(one)), p2 of (x := G, y := zero, z := not(one)))
    thenHave(I(gamma) <= NI(N)) by Substitution.ApplyRules(IN)
    have(thesis) by Tautology.from(lastStep, IS of (delta := N))
  }


  val leftAnd = Theorem(S(L(x), delta) \/ S(L(y), delta) |- S(L(x n y), delta)) {
    val leftAnd1 = have(S(L(x), delta) |- S(L(x n y), delta)) subproof {
      have(S(L(x n y), R(x))) by Tautology.from(p4a, SLR of(x := (x n y), y := x))
      have(thesis) by Tautology.from(lastStep, cut of (gamma := L(x n y)))
    }
    val leftAnd2 = have(S(L(y), delta) |- S(L(x n y), delta)) subproof {
      have(S(L(x n y), R(y))) by Tautology.from(p5a, SLR of (x := (x n y)))
      have(thesis) by Tautology.from(lastStep, cut of(gamma := L(x n y), x := y))
    }
    have(thesis) by Tautology.from(leftAnd1, leftAnd2)
  }

  val leftOr = Theorem((S(L(x), delta), S(L(y), delta)) |- S(L(x u y), delta)) {
    assume(S(L(x), delta) /\ S(L(y), delta))
    have((x <= NI(delta)) /\ (y <= NI(delta))) by Tautology.from(SLF, SLF of (x := y))
    have((x u y) <= NI(delta)) by Tautology.from(lastStep, p6b of (z := NI(delta)))
    thenHave(I(L(x u y)) <= NI(delta)) by Substitution.ApplyRules(IL)
    have(thesis) by Tautology.from(lastStep, IS of (gamma := L(x u y)))
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

  val rightOr = Theorem(S(gamma, R(x)) \/ S(gamma, R(y)) |- S(gamma, R(x u y))) {
    val rightOr1 = have(S(gamma, R(x)) |- S(gamma, R(x u y))) subproof {
      have(S(L(x), R(x u y))) by Tautology.from(p4b, SLR of (y := (x u y)))
      have(thesis) by Tautology.from(lastStep, cut of (delta := R(x u y)))
    }
    val rightOr2 = have(S(gamma, R(y)) |- S(gamma, R(x u y))) subproof {
      have(S(L(y), R(x u y))) by Tautology.from(p5b, SLR of(x := y, y := (x u y)))
      have(thesis) by Tautology.from(lastStep, cut of(x := y, delta := R(x u y)))
    }
    have(thesis) by Tautology.from(rightOr1, rightOr2)
  }

  val rightNot = Theorem(S(L(x), delta) |- S(R(not(x)), delta)) {
    have(S(R(not(x)), R(x))) by Tautology.from(p7b, SRR of (x := not(x), y := x))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := R(not(x))))
  }


  var log = false

  object RestateWithAxioms extends ProofTactic:

    def apply(using lib: library.type, proof: lib.Proof)
             (bot: Sequent): proof.ProofTacticJudgement = from()(bot)

    // TODO only take axioms from bot.left ?
    //  or also take refs to other proof steps which can then be cut ?

    def from(using lib: library.type, proof: lib.Proof)
            (axioms: Formula*)(bot: Sequent): proof.ProofTacticJudgement =
//      if bot.left.nonEmpty || bot.right.size != 1 then // AR
      if bot.right.size != 1 then
        proof.InvalidProofTactic("Only support goals of the form ??? |- left <= right")
      else bot.right.head match
        case (left <= right) =>
          // TODO? also split bot.left conjonctions ?
          withParameters(axioms ++ bot.left *)(left, right)
        case _ => proof.InvalidProofTactic("Only support goals of the form () |- left <= right")


    /**
     * @param axioms of the forms (F(x), G(y))
     * Produce proof of: axioms |- left <= right
     */
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (axioms: Formula*)(left: Term, right: Term): proof.ProofTacticJudgement =

      // IMPROVE refactor common
      val axiomsS: Set[Formula] = axioms.toSet.collect {
        case (`one` <= `zero`) => S(N,       N       )
        case (`one` <= right ) => S(N,       R(right))
        case (left  <= `zero`) => S(L(left), N       )
        case (left  <= right ) => S(L(left), R(right))
      }

      // IMPROVE merge when can
      val axFormulas: Set[Term] = axiomsS
        .flatMap { case S(gamma1, delta1) => Set(gamma1, delta1) }
        .collect { case L(x) => x case R(x) => x }

      // IMPROVE
      val cache = mMap[(Term, Term), Any]()

      var ident = 0

      def canProve(using proof: lib.Proof)(gamma1: Term, delta1: Term): Boolean = prove(gamma1, delta1).isValid

      def prove(using proof: lib.Proof)(gamma1: Term, delta1: Term): proof.ProofTacticJudgement =
        cache.get(gamma1, delta1) match
          case Some(cachedCorrectType: proof.ProofTacticJudgement) => cachedCorrectType
          case Some(r) if !r.asInstanceOf[proof.ProofTacticJudgement].isValid =>
            r.asInstanceOf[proof.ProofTacticJudgement]
            // NOTE works to avoid cycle but a ValidProofTactic with different fail so the current implementation does it again
          case _ =>
//            if log then
//              println(" ".repeat(ident) + s"== starting prove($gamma1, $delta1)")
//            println(s"cache: $cache")
            ident += 1

            cache.addOne((gamma1, delta1), proof.InvalidProofTactic(s"Starting prove($gamma1, $delta1)"))
            val r = proveNoC(gamma1, delta1)
            cache.addOne((gamma1, delta1), r)

            ident -= 1
            if log then r match
              case proof.ValidProofTactic(bot, _, _) =>
                println(" ".repeat(ident) + s"== endded prove($gamma1, $delta1) Valid")
              case _ =>
//                  println(" ".repeat(ident) + s"== ended prove($gamma1, $delta1) Invalid")
            r

      // TODO RM can use Tautology (exp) in prove ?
      // proove () |- S(gamma, delta) if can
      def proveNoC(using proof: lib.Proof)(gamma1: Term, delta1: Term): proof.ProofTacticJudgement = TacticSubproof:
        val goal: Sequent = axiomsS |- S(gamma1, delta1)
        (gamma1, delta1) match

          // Hyp
          case (L(x1), R(y)) if x1 == y =>
            have(goal) by Tautology.from(hyp of (x := x1))

          // Ax
          case (gamma1, delta) if axiomsS.contains(S(gamma1, delta1)) =>
            have(goal) by RewriteTrue

          // Weaken
          case (gamma1, delta1) if gamma1 != N && delta1 != N && canProve(gamma1, N) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, N)),
              weaken of (gamma := gamma1, delta := delta1),
            )

          // Contration
          case (gamma1, N) if canProve(gamma1, gamma1) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, gamma1)),
              contraction of (gamma := gamma1),
            )

          // LeftNot
          case (gamma1, L(not(x1))) if canProve(gamma1, R(x1)) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, R(x1))),
              leftNot of (gamma := gamma1, x := x1),
            )

          // LeftAnd
          case (L(x1 n y1), delta1) if canProve(L(x1), delta1) =>
            have(goal) by Tautology.from(
              have(prove(L(x1), delta1)),
              leftAnd of(x := x1, y := y1, delta := delta1)
            )
          case (L(x1 n y1), delta1) if canProve(L(y1), delta1) =>
            have(goal) by Tautology.from(
              have(prove(L(y1), delta1)),
              leftAnd of(x := x1, y := y1, delta := delta1)
            )

          // LeftOr
          case (L(x1 u y1), delta1) if canProve(L(x1), delta1) && canProve(L(y1), delta1) =>
            have(goal) by Tautology.from(
              have(prove(L(x1), delta1)), have(prove(L(y1), delta1)),
              leftOr of(x := x1, y := y1, delta := delta1)
            )

          // RightNot
          case (R(not(x1)), delta1) if canProve(L(x1), delta1) =>
            have(goal) by Tautology.from(
              have(prove(L(x1), delta1)),
              rightNot of(delta := delta1, x := x1),
            )

          // RightAnd
          case (gamma1, R(x1 n y1)) if canProve(gamma1, R(x1)) && canProve(gamma1, R(y1)) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, R(x1))), have(prove(gamma1, R(y1))),
              rightAnd of(x := x1, y := y1, gamma := gamma1)
            )

          // RightOr
          case (gamma1, R(x1 u y1)) if canProve(gamma1, R(x1)) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, R(x1))),
              rightOr of(x := x1, y := y1, gamma := gamma1),
            )
          case (gamma1, R(x1 u y1)) if canProve(gamma1, R(y1)) =>
            have(goal) by Tautology.from(
              have(prove(gamma1, R(y1))),
              rightOr of(x := x1, y := y1, gamma := gamma1),
            )

          // AxCut
          case (gamma1, delta1) if axFormulas.exists(x1 => canProve(gamma1, R(x1)) && canProve(L(x1), delta1)) =>
            LazyList.from(axFormulas)
              .map { x1 => (x1, (prove(gamma1, R(x1)), prove(L(x1), delta1))) }
              .collectFirst { case (x1, (s1, s2)) if s1.isValid && s2.isValid =>
                have(goal) by Tautology.from(
                  have(s1), have(s2),
                  cut of(gamma := gamma1, x := x1, delta := delta1)
                )
              }.get

          // Try by flipping delta1, gamma1
          case (gamma1, delta1) if canProve(delta1, gamma1) =>
            have(goal) by Tautology.from(
              have(prove(delta1, gamma1)),
              commutS of(gamma := gamma1, delta := delta1)
            )

          case _ => return proof.InvalidProofTactic(s"No rules applied to $gamma1, $delta1")

      end proveNoC

      val left1 = if left == one then N else L(left)
      val right1 = if right == zero then N else R(right)

      prove(left1, right1) andThen2 { lastStep => // axiomsS |- S(left1, right1)
        val s1 = have(axiomsS |- left <= right) by Tautology.from(lastStep,
          SLR of(x := left, y := right),
          SLN of (x := left), SNR of (y := right), SNN
        )
        have(axioms |- left <= right) by Tautology.from(
          s1 +: axioms.collect {
            case (`one` <= `zero`) => SNN
            case (`one` <= r) => SNR of (y := r)
            case (l <= `zero`) => SLN of (x := l)
            case (l <= r) => SLR of (x := l, y := r)
          } *
        )
      }

    end withParameters

  end RestateWithAxioms

//  log = true

  val test1 = Theorem(x <= x) {

//    val s1 = have(x <= x |- S(L)) subproof { sorry }
//    val s2 = have(x <= x |- x <= z) subproof { sorry }
//    have

    have(thesis) by RestateWithAxioms.from()
  }

  val test2a = Theorem((x n (not(x))) <= zero) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test2 = Theorem(x <= (x u y)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test3 = Theorem((y n x) <= y) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test3b = Theorem((y n x) <= x) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test4 = Theorem((x n y) <= (y u z)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test5 = Theorem(one <= x |- not(x) <= zero) {
    have(thesis) by RestateWithAxioms.apply
  }

  val a1 = one <= (x n (not(x) u z))

  val testPaperExampleWithSomeHelp = Theorem(a1 |- one <= z) {
    val f1 = one <= (not(x) u z)
    val f2 = (not(x) u z) <= z

    // NOTE not needed but usefull for testing

    val s1 = have(a1 |- f1) by RestateWithAxioms.apply // Ok

    val s2 = have(a1 |- f2) subproof {
//      have((x n (not(x) u z)) <= x) by RestateWithAxioms.apply
//      have(a1 |- one <= x) by RestateWithAxioms.apply // Ok
      have(thesis) by RestateWithAxioms.apply
    }

    have(thesis) by RestateWithAxioms.apply
  }

  val testPaperExample = Theorem(a1 |- one <= z) {
    have(thesis) by RestateWithAxioms.apply
  }


end OrthologicWithAxiomsI2
