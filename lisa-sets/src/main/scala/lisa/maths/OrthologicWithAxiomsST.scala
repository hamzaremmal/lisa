package lisa.maths

import lisa.fol.FOL as F
import lisa.maths.settheory.SetTheory.*
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicWithAxiomsST extends lisa.Main:

  // ortholattice signature
  val U = variable
  val <= = variable
  val n, u, not = variable
  val `0`, `1` = variable

  // ortholattice elements
  val x, y, z = variable

  extension(left: Term)
    def <=(right: Term): Formula = in(pair(left, right), OrthologicWithAxiomsST.<=)
    def n(right: Term): Term = app(OrthologicWithAxiomsST.n, pair(left, right))
    def u(right: Term): Term = app(OrthologicWithAxiomsST.u, pair(left, right))

  // AR needs inline ?
  def /(t: Term): Term = app(OrthologicWithAxiomsST.not, t)


//  inline def forallInS(x: Variable, f: Formula): Formula = ∀(x, (x ∈ S) ==> f)
  inline def ∀!(x: Variable, f: Formula) = forallInU(x)(f)

  def forallInU(xs: Variable*)(f: Formula): Formula = xs match
    case Seq() => f
    case x +: xs => ∀(x, (x ∈ U) ==> forallInU(xs*)(f))


  // ASK type-checking ?
  val p0: ConstantPredicateLabel[7] = DEF(U, <=, n, u, not, `0`, `1`) -->
    relationBetween(<=, U, U) /\ functionalOver(n, U)


  // CHECK is actually using the def argument
  val p1: ConstantPredicateLabel[2] = DEF(U, <=) --> ∀(x, (x ∈ U) ==> x <= x)

//  val p2: ConstantPredicateLabel[2] = DEF(S, <=) -->
//    ∀!(x, ∀!(y, ∀!(z, (x <= y) /\ (y <= z) ==> (x <= z))))
//  val p3a: ConstantPredicateLabel[3] = DEF(S, <=, `0`) --> ∀!(x, (`0` <= x))

  val p2: ConstantPredicateLabel[2] = DEF(U, <=) --> forallInU(x, y, z) { (x <= y) /\ (y <= z) ==> x <= z }

  val p3a: ConstantPredicateLabel[3] = DEF(U, <=, `0`) --> ∀!(x, `0` <= x)
  val p3b: ConstantPredicateLabel[3] = DEF(U, <=, `1`) --> ∀!(x, x <= `1`)

  val p4a: ConstantPredicateLabel[3] = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= x }
  val p5a: ConstantPredicateLabel[3] = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= y }

  val p4b: ConstantPredicateLabel[3] = DEF(U, <=, u) --> forallInU(x, y) { x <= (x u y) }
  val p5b: ConstantPredicateLabel[3] = DEF(U, <=, u) --> forallInU(x, y) { y <= (x u y) }

  val p6a: ConstantPredicateLabel[3] = DEF(U, <=, n) --> forallInU(x, y, z) { (x <= y) /\ (x <= z) ==> x <= (y n z) }
  val p6b: ConstantPredicateLabel[3] = DEF(U, <=, u) --> forallInU(x, y, z) { (x <= z) /\ (x <= z) ==> (x u y) <= z }

  val p7a: ConstantPredicateLabel[3] = DEF(U, <=, not) --> forallInU(x) { x <= /(/(x)) }
  val p7b: ConstantPredicateLabel[3] = DEF(U, <=, not) --> forallInU(x) { /(/(x)) <= x }

  val p8: ConstantPredicateLabel[3] = DEF(U, <=, not) --> forallInU(x, y) { x <= y ==> /(y) <= /(x) }

  val p9a: ConstantPredicateLabel[5] = DEF(U, <=, n, not, `0`) --> forallInU(x) { (x n /(x)) <= `0` }
  val p9b: ConstantPredicateLabel[5] = DEF(U, <=, u, not, `1`) --> forallInU(x) { `1` <= (x u /(x)) }

  // FIX
//  val isOrthollatice: ConstantPredicateLabel[7] = DEF(U, <=, n, u, not, `0`, `1`) --> And(Seq(
  val isOrthollatice: ConstantPredicateLabel[5] = DEF(U, <=, n, u, not) --> And(Seq(
    p1(U, <=),
    p2(U, <=),
//    p3a(U, <=, `0`), p3b(U, <=, `1`),
    p4a(U, <=, n), p4b(U, <=, u),
    p5a(U, <=, n), p5b(U, <=, u),
    p6a(U, <=, n), p6b(U, <=, u),
    p7a(U, <=, not), p7b(U, <=, not),
    p8(U, <=, not),
//    p9a(U, <=, n, not, `0`), p9b(U, <=, u, not, `1`)
  ))


  // IMPROVE with tactic InstantiateForallInU
  object InstantiateForallIn extends ProofTactic:

    // TODO take U as arg
    def apply(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(x: F.Variable) // AR need to take U as arg ?
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val prem = proof.getSequent(premise)
//      val assumptions: Set[Formula] = prem.left
//        .collect { case AppliedConnector(F.And, fs) => fs case f => Set(f) }.flatten // ASK
//      println(s"assumptions: $assumptions")
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


  val isO = isOrthollatice(U, <=, n, u, not)
  val isInU: F.Formula = (x ∈ U) /\ (y ∈ U) /\ (z ∈ U)
  val isInUs: Seq[F.Formula] = Seq((x ∈ U), (y ∈ U), (z ∈ U))


  val meetInU = Theorem(isO /\ isInU |- (x u y) ∈ U) {
    sorry
  }

  //  val p1: ConstantPredicateLabel[2] = DEF(U, <=) --> ∀(x, (x ∈ U) ==> x <= x)
  val p1InU = Theorem(isO /\ isInU |- (x u y) ∈ U) {

    // OK
//    val s1 = have((x ∈ U) |- ∀(x, (x ∈ U) ==> x <= x)) subproof { sorry }
//    InstantiateForallInU.apply(U)(x)(s1)((x ∈ U) |- x <= x)

    // OK
//    have(((x ∈ U), (y ∈ U)) |- ∀(x, (x ∈ U) ==> x <= x)) subproof { sorry }
//    thenHave(((x ∈ U), (y ∈ U)) |- x <= x) by InstantiateForallIn(U)(x)

    // OK
    assume(isInUs*)
    have(∀(x, (x ∈ U) ==> x <= x)) subproof { sorry }
    thenHave(x <= x) by InstantiateForallIn(U)(x)

//    have((x ∈ U) |- x <= x)

    sorry
  }

  val p2InU = Theorem(isO /\ isInU |- (x <= y) /\ (y <= z) ==> x <= z) {
    sorry
  }

  val p4aInU = Theorem(isO /\ isInU |- (x n y) <= x) {
    assume(isO /\ isInU)
    have(p4a(U, <=, n)) by Tautology.from(isOrthollatice.definition)
    have(forallInU(x, y) { (x n y) <= x }) by Tautology.from(lastStep, p4a.definition)
    thenHave(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x))) by Restate
    thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x)) by InstantiateForall(x)
    thenHave(∀(y, (y ∈ U) ==> (x n y) <= x)) by Tautology
    thenHave((y ∈ U) ==> (x n y) <= x) by InstantiateForall(y)
    thenHave((x n y) <= x) by Tautology
  }

  val LeftAndL = Theorem(isO /\ isInU /\ (x <= z) |- (x n y) <= z) {
    assume(isO /\ isInU)
    have((x n y) <= x) by Restate.from(p4aInU)
//    have()
//    have(((x n y) <= x) /\ (y <= z) ==> x <= z) by Restate.from(p4aInU of (x := (x n y)))
    sorry
  }





end OrthologicWithAxiomsST