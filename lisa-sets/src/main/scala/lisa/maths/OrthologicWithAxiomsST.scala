package lisa.maths

import collection.mutable.Map as mMap
import lisa.fol.FOL as F
import lisa.maths.settheory.SetTheory.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{ProofSequentTactic, ProofTactic}

object OrthologicWithAxiomsST extends lisa.Main:

  // ortholattice signature
  val S, T, U = variable
  val <= = variable
  val n, u, not = variable
  val `0`, `1` = variable

  // ortholattice elements
  val v, w, x, y, z = variable

  // needed for subst in defs from maths.SetTheory
  val f, t, a, r = variable

  extension(left: Term)
    def <=(right: Term): Formula = in(pair(left, right), OrthologicWithAxiomsST.<=)
    def n(right: Term): Term = app(OrthologicWithAxiomsST.n, pair(left, right))
    def u(right: Term): Term = app(OrthologicWithAxiomsST.u, pair(left, right))
    def unary_! = app(OrthologicWithAxiomsST.not, left)

  // RN ; AR needs inline ?
  def /(t: Term): Term = app(OrthologicWithAxiomsST.not, t)

  def forallInU(xs: Variable*)(f: Formula): Formula =
    xs.foldRight(f) { (x, g) => ∀(x, (x ∈ U) ==> g) }


  // ASK if ok
  val p0: ConstantPredicateLabel[5] = DEF(U, <=, n, u, not) -->
    relationBetween(<=, U, U) /\
    functionFrom(not, U, U) /\
    functionFrom(n, cartesianProduct(U, U), U) /\
    functionFrom(u, cartesianProduct(U, U), U)

  // CHECK is actually using the def argument
  val p1: ConstantPredicateLabel[2] = DEF(U, <=) --> forallInU(x) { x <= x }

  val p2: ConstantPredicateLabel[2] = DEF(U, <=) --> forallInU(x, y, z) { (x <= y) /\ (y <= z) ==> x <= z }

  val p3a: ConstantPredicateLabel[3] = DEF(U, <=, `0`) --> forallInU(x) { `0` <= x }
  val p3b: ConstantPredicateLabel[3] = DEF(U, <=, `1`) --> forallInU(x) { x <= `1` }

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
  val isOrthollatice: ConstantPredicateLabel[7] = DEF(U, <=, n, u, not, `0`, `1`) --> And(Seq(
    p0(U, <=, n, u, not),
    p1(U, <=),
    p2(U, <=),
    p3a(U, <=, `0`), p3b(U, <=, `1`),
    p4a(U, <=, n), p4b(U, <=, u),
    p5a(U, <=, n), p5b(U, <=, u),
    p6a(U, <=, n), p6b(U, <=, u),
    p7a(U, <=, not), p7b(U, <=, not),
    p8(U, <=, not),
    p9a(U, <=, n, not, `0`), p9b(U, <=, u, not, `1`)
  ))

  object SimpleInstantiateForallIn extends ProofTactic:

    def apply1(using lib: library.type, proof: lib.Proof)
              (U: F.Variable)(x: F.Variable)
              (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      require(bot.right.size == 1)

      val bot1 = bot.left |- (x ∈ U) ==> bot.right.head

      TacticSubproof:
        val s1 = have(bot1) by InstantiateForall(x)(premise)
        have(bot) by Tautology.from(s1) // AR !!
    // TODO err messages

    end apply1


    def apply(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(xs: F.Variable*)
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

//      xs.foldRight(premise) { case (x, lastStep) =>
//
//        val bot1 = ???
//        apply1(U)(x)(lastStep)
//
//      }
      ???

    end apply

  end SimpleInstantiateForallIn

  // IMPROVE with tactic InstantiateForallInU
  object InstantiateForallIn extends ProofTactic:

    def applyM2(using lib: library.type, proof: lib.Proof)
              (U: F.Variable)(xs: F.Variable*)
              (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      ???

    def applyM(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(xs: F.Variable*)
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      val premiseSequent = proof.getSequent(premise)

      if premiseSequent.right.size != 1 then
        proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
      else
        val phi: F.Formula = premiseSequent.right.head

//        xs.foldLeft(phi) { case (phi1, x) => ??? }
        def rec(acc: proof.ProofTacticJudgement, phi: F.Formula, xs: Seq[F.Variable]): proof.ProofTacticJudgement  =
          xs match
            case Seq() =>
              acc andThen2 { lastStep =>
                have(bot) by Tautology.from(premise, lastStep)
              }

            case x +: xs =>
              println(s"x: $x, phi: $phi")
              val xInU: F.Formula = F.AppliedPredicate(`in`, Seq(x, U))
              if !premiseSequent.left.contains(xInU) then
                proof.InvalidProofTactic(s"LHS of premise sequent does not contain ($x ∈ $U).")
              else
                phi match
                  case F.BinderFormula(F.Forall, `x`, phiBody @ F.AppliedConnector(F.Implies, Seq(`xInU`, phiBody2))) =>
                    println(s"phiBody2: $phiBody2")
                    val acc1 = acc andThen2 { lastStep =>
                      println(s"lastStep: ${lastStep.asInstanceOf[proof.ProofStep].bot}")
                      val s1 = have(premiseSequent.left |- phiBody) by Tautology.from(premise, lastStep) // AR need premise everywhere ?
                      have(premiseSequent.left |- phiBody2) by Tautology.from(premise, s1)
                    }
                    rec(acc1, phiBody2, xs)
                  case _ => proof.InvalidProofTactic(s"RHS of premise sequent malformed.") // RN

        val i = proof.ValidProofTactic(
          premiseSequent, // Ar ungly
          Seq(K.Restate(premiseSequent.underlying, -1)),
          Seq(premise)
        )
        rec(i, phi, xs)


    // TODO take U as arg ?
    def apply(using lib: library.type, proof: lib.Proof)
             (U: F.Variable)(x: F.Variable)
             (premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val prem = proof.getSequent(premise)
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


  val isO = isOrthollatice(U, <=, n, u, not, `0`, `1`)

  def inU(xs: Term*): Seq[F.Formula] = xs.map(_ ∈ U)

  val appInDom = Theorem((functionFrom(f, U, T), (x ∈ U)) |- (app(f, x) ∈ T)) {
    assume(functionFrom(f, U, T))

    val s1 = have(f ∈ setOfFunctions(U, T)) by Tautology.from(functionFrom.definition of (x := U, y := T))

    val s2 = have(∀(t, in(t, setOfFunctions(U, T)) <=> (in(t, powerSet(cartesianProduct(U, T))) /\ functionalOver(t, U)))) by InstantiateForall(setOfFunctions(U, T))(setOfFunctions.definition of (x := U, y := T))
    thenHave(in(f, setOfFunctions(U, T)) <=> (in(f, powerSet(cartesianProduct(U, T))) /\ functionalOver(f, U))) by InstantiateForall(f)
//    have(in(f, setOfFunctions(U, T)) <=> (in(f, powerSet(cartesianProduct(U, T))) /\ functionalOver(f, U))) by InstantiateForall(setOfFunctions(U, T), f)(setOfFunctions.definition of (x := U, y := T)) // ASK

    have(in(f, powerSet(cartesianProduct(U, T))) /\ functionalOver(f, U)) by Tautology.from(lastStep, s1)


    sorry
  }

  val meetInU = Theorem(isO +: inU(x, y) |- (x u y) ∈ U) {
    sorry
  }
  val joinInU = Theorem(isO +: inU(x, y) |- (x n y) ∈ U) {
    sorry
  }
  val notInU = Theorem(isO +: inU(x) |- !x ∈ U) {
//    assume(isO +: isInUs *)
//    val s1 = have(functionalOver(not, U)) by Tautology.from(isOrthollatice.definition, p0.definition)
//    val s2 = have(relationDomain(not) === U) by Tautology.from(s1, functionalOver.definition of (f := not, x := U))
//
//    val s3 = have((relationDomain(not) === U) <=> (∀(t, in(t, U) <=> ∃(a, in(pair(t, a), not))))) by
//      InstantiateForall(U)(relationDomain.definition of (r := not)) // AR simplify ?
//
//    have(∀(t, in(t, U) <=> ∃(a, in(pair(t, a), not)))) by Tautology.from(s2, s3)
//    thenHave(in(/(x), U) <=> ∃(a, in(pair(/(x), a), not))) by InstantiateForall(/(x))
//
////    thenHave(in(/(x), U) <=> in(pair(/(x), a), not)) by (/(x))
//
//    have(pair(x, app()))
//
////    have(∀(t, in(t, U) <=> ∃(a, in(pair(t, a), r))))
////    have(∀(t, in(t, z) <=> ∃(a, in(pair(t, a), r))))
//
////    have((app(not, x) === y) <=> ((functional(not) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅))) by
////      InstantiateForall(U)(relationDomain.definition of (r := not)) // AR simplify ?
//
//    have(in(app(not, x), U))
    sorry
  }


  /** Axioms with inU .. as premises **/

  /*
  val p1InU = Theorem(isO +: inU(x) |- x <= x) {
    assume(isO, x ∈ U)
    val s1 = have(∀(x, (x ∈ U) ==> x <= x)) by Tautology.from(isOrthollatice.definition, p1.definition)
    thenHave(x <= x) by SimpleInstantiateForallIn.apply1(U)(x) // AR
//    have(x <= x) by InstantiateForallIn(U)(x)(s1)
  }

  val p2InU = Theorem(isO +: inU(x, y, z) :+ (x <= y) :+ (y <= z) |- x <= z) {
    assume(isO +: isInUs *)

    have(forallInU(x, y, z) { (x <= y) /\ (y <= z) ==> x <= z }) by Tautology.from(isOrthollatice.definition, p2.definition)

    // OK
    thenHave(forallInU(y, z) { (x <= y) /\ (y <= z) ==> x <= z }) by InstantiateForallIn(U)(x)
    thenHave(forallInU(z) { (x <= y) /\ (y <= z) ==> x <= z }) by InstantiateForallIn(U)(y)
    thenHave((x <= y) /\ (y <= z) ==> x <= z) by InstantiateForallIn(U)(z)

    // NOT ok
//    thenHave(forallInU(z) { (x <= y) /\ (y <= z) ==> x <= z }) by InstantiateForallIn.applyM(U)(x, y)
  }

  val p4aInU = Theorem(isO +: inU(x, y) |- (x n y) <= x) {
//    assume(isO +: isInUs *)
//    have(p4a(U, <=, n)) by Tautology.from(isOrthollatice.definition)
//    have(forallInU(x, y) { (x n y) <= x }) by Tautology.from(lastStep, p4a.definition)
////    thenHave(∀(x, (x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x))) by Restate
////    thenHave((x ∈ U) ==> ∀(y, (y ∈ U) ==> (x n y) <= x)) by InstantiateForall(x)
//    thenHave(∀(y, (y ∈ U) ==> (x n y) <= x)) by InstantiateForallIn(U)(x)
////    thenHave((y ∈ U) ==> (x n y) <= x) by InstantiateForall(y)
//    thenHave((x n y) <= x) by InstantiateForallIn(U)(y)
    sorry
  }

  val p5aInU = Theorem(isO +: inU(x, y) |- (x n y) <= y) {
    sorry
  }

  val p6aInU = Theorem(isO +: inU(x, y, z) |- (x <= y) /\ (x <= z) ==> (x <= (y n z))) {
    sorry
  }

  val p6bInU = Theorem(isO +: inU(x, y, z) |- (x <= z) /\ (y <= z) ==> (x u y) <= z) {
    sorry
  }

  val p7bInU = Theorem(isO +: inU(x) |- /(/(x)) <= x) {
    sorry
  }

  val p8aInU = Theorem(isO +: inU(x, y) :+ (x <= y) |- /(y) <= /(x)) {
    sorry
  }
  */

  /** RULES **/

  val hyp = Theorem(isO +: inU(x) |- x <= x) {
//    have(thesis) by Restate.from(p1InU)
    sorry
  }

  val cut = Theorem(isO +: inU(x, y, z) :+ (x <= y) :+ (y <= z) |- (x <= z)) {
//    have(thesis) by Tautology.from(p2InU)
    sorry
  }

  val weaken1 = Theorem(isO +: inU(x, y) :+ (x <= `0`) |- x <= y) { sorry }
  val weaken2 = Theorem(isO +: inU(x, y) :+ (`1` <= y) |- x <= y) { sorry }

  val contraction1 = Theorem(isO +: inU(x) :+ (x <= !x) |- x <= `0`) { sorry }
  val contraction2 = Theorem(isO +: inU(x) :+ (!x <= x) |- `1` <= x) { sorry }

  val leftAnd1 = Theorem(isO +: inU(x, y, z) :+ (x <= z) |- (x n y) <= z) {
//    assume(isO +: inU(x, y, z) *)
//    have((x n y) ∈ U) by Restate.from(joinInU)
//    have(((x n y) <= x) /\ (x <= z) ==> (x n y) <= z) by Tautology.from(lastStep, p2InU of (x := (x n y), y := x))
//    have(thesis) by Tautology.from(lastStep, p4aInU)
    sorry
  }
  val leftAnd2 = Theorem(isO +: inU(x, y, z) :+ (y <= z) |- (x n y) <= z) {
//    assume(isO +: inU(x, y, z) *)
//    have((x n y) ∈ U) by Restate.from(joinInU)
//    have(((x n y) <= y) /\ (y <= z) ==> (x n y) <= z) by Tautology.from(lastStep, p2InU of (x := (x n y)))
//    have(thesis) by Tautology.from(lastStep, p5aInU)
    sorry
  }

  val leftOr = Theorem(isO +: inU(x, y, z) :+ (x <= z) :+ (y <= z) |- (x u y) <= z) {
//    have(thesis) by Restate.from(p6bInU)
    sorry
  }

  val rightAnd = Theorem(isO +: inU(x, y, z) :+ (x <= y) :+ (x <= z) |- x <= (y n z)) { sorry }

  val rightOr1 = Theorem(isO +: inU(x, y, z) :+ (x <= y) |- x <= (y u z)) { sorry }
  val rightOr2 = Theorem(isO +: inU(x, y, z) :+ (x <= z) |- x <= (y u z)) { sorry }

  val commutRL = Theorem(isO +: inU(x, y) :+ (!x <= !y) |- y <= x) { sorry }
  val commutLL = Theorem(isO +: inU(x, y) :+ (x <= !y) |- y <= !x) { sorry }
  val commutRR = Theorem(isO +: inU(x, y) :+ (!x <= y) |- !y <= x) { sorry }


  object Singleton:
    def unapply(t: F.Term): Option[F.Term] = t match
      case unorderedPair(x1, x2) if x1 == x2 => Some(x1)
      case _ => None

  object Pair:
    def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
      case unorderedPair(unorderedPair(x1, y1), Singleton(x2)) if x1 == x2 => Some((x1, y1))

  object App:
    def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
      case AppliedFunction(`app`, Seq(fun, arg)) => Some((fun, arg))
      case _ => None


  object RestateWithAxioms extends ProofTactic:


    // IMPROVE such that do not neet to write .apply
    // isOrthollatice(U, <=, n, u, not) |- left <= right
    def apply(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =

      // AR
      val leq = OrthologicWithAxiomsST.<=
      val meet = OrthologicWithAxiomsST.n
      val not0 = OrthologicWithAxiomsST.not // RN

      object Leq:
        def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
          case in(Pair(l, r), `leq`) => Some((l, r))
          case _ => None

      object Meet:
        def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
          case App(`meet`, Pair(x, y)) => Some((x, y))
          case _ => None

      object Not:
        def unapply(t: F.Term): Option[F.Term] = t match
          case App(`not0`, x) => Some(x)
          case _ => None

      enum Annotated:
        case L(t: F.Term)
        case R(t: F.Term)
        case N
      import Annotated.*

      extension (a: Annotated)
        def pos1: Term = a match
          case L(t) => t case R(t) => /(t) case N => `1`
        def pos2: Term = a match
          case L(t) => /(t) case R(t) => t case N => `0`

      // MV to proveNoC start a vals
      object P1:
        def unapply(a: Annotated): Some[F.Term] = Some(a.pos1)
      object P2:
        def unapply(a: Annotated): Some[F.Term] = Some(a.pos2)

      val cache = mMap[(Annotated, Annotated), Any]()

      def prove(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement =
        cache.get(gamma, delta) match
          case Some(cachedSamePath: proof.ProofTacticJudgement) =>
            cachedSamePath
          case Some(r) if r.isInstanceOf[proof.InvalidProofTactic] =>
            r.asInstanceOf[proof.ProofTacticJudgement]
            // NOTE works to avoid cycles but doesn't reuse a ValidProofTactic with different path
          case _ =>
            println(s"== starting prove($gamma, $delta)")
            cache.addOne((gamma, delta), proof.InvalidProofTactic(s"Starting prove($gamma, $delta)"))
            val res: proof.ProofTacticJudgement = proveNoC(gamma, delta)
            cache.addOne((gamma, delta), res)
            println(s"== ending prove($gamma, $delta) with ${res.isValid}")
            res
      end prove

      def proved(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): Boolean = prove(gamma, delta).isValid

      // IMPROVE by
      //  - rm nesting of subproofs
      //  - rm as mush as can premises of the form isInU

      /*
      L(x) delta --> x <= I(delta)
      gamma R(x) --> I(gamma) <= x

      AR assuming never
      N L
      R N
      * */

      // prove isO /\ ... in universe |- gamma delta
      def proveNoC(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement = TacticSubproof:
        assume(isO)

        val gammaF = gamma.pos1 // AR use more
        val deltaF = delta.pos2 // AR use more
        val goalRight = gammaF <= deltaF

        (gamma, delta) match

          case (L(x1), R(y1)) if x1 == y1 =>
            have(inU(x1) |- (x1 <= y1)) by Restate.from(hyp of (x := x1))

          /** Deconstructing L **/

          // Weaken TODO
          case (L(x1), delta) if delta != N && proved(L(x1), N) && false => ???

          // Contraction
          case (L(x1), N) if proved(L(x1), L(x1)) && false => ???

          // LeftNot
          case (L(Not(x1)), delta) if proved(R(x1), delta) =>
            have(prove(R(x1), delta))

          // LeftAnd
          case (L(Meet(x1, y1)), delta @ P2(z1)) if proved(L(x1), delta) =>
            val s1 = have(prove(L(x1), delta))
            have(inU(x1, y1, z1) |- (x1 n y1) <= z1) by Cut(s1, leftAnd1 of (x := x1, y := y1, z := z1))
          case (L(Meet(x1, y1)), delta @ P2(z1)) if proved(L(y1), delta) =>
            val s1 = have(prove(L(y1), delta))
            have(inU(x1, y1, z1) |- (x1 n y1) <= z1) by Cut(s1, leftAnd2 of(x := x1, y := y1, z := z1))

          // TODO
          case (gamma, L(x1)) if proved(L(x1), gamma) && false =>
            val s1 = have(prove(L(x1), gamma)) // x1 <= gamma.pos2

//            assume(gamma != N)
            gamma match
              case L(y1) =>
//                have(y1 <= !x1)
                ???
              case R(y1) => ???

          /** Deconstructing R **/

          // AR is diff order problematic
          // Weaken TODO
          case (gamma, R(y1)) if gamma != N && proved(N, R(y1)) && false => ???

          // Contraction TODO
          case (N, R(y1)) if proved(R(y1), R(y1)) && false => ???
          
          // RightNot
          case (gamma, R(Not(x1))) if proved(gamma, L(x1)) =>
            have(prove(gamma, L(x1)))

          // TODO
          case (R(x1), delta) if proved(delta, R(x1)) && false =>
            val s1 = have(prove(delta, R(x1))) // delta.pos1 <= x1
            have(s1.bot.left |- /(x1) <= /(deltaF)) by Cut(s1, p8aInU of(x := deltaF, y := x1))

            delta match
              case L(y1) =>
                have(s1.bot.left |- /(x1) <= /(y1)) by Cut(s1, p8aInU of(x := y1, y := x1))

              case R(y1) =>
                // s1: /(y1) <= x1
                have(inU(y1) |- /(/(y1)) <= y1) by Restate.from(p7bInU of (x := y1))
//                have(/(x1) <= )
                //                have(/(x1) <= y1) by (s1)
                ???

              case N =>
                ???

          // TODO flip others too ?
          case (R(x1), L(y1)) if proved(L(y1), R(x1)) =>
            val s1 = have(prove(L(y1), R(x1)))
            have(/(x1) <= /(y1)) by Cut(s1, p8aInU of(x := y1, y := x1))

          case (gamma, delta) => return proof.InvalidProofTactic(s"No rules applied to $gamma, $delta") // RN?

      end proveNoC

      if bot.right.size != 1 then
        proof.InvalidProofTactic("Only support goals of the form ??? |- left <= right")
      else bot.right.head match
        case in(Pair(left, right), `leq`) => prove(L(left), R(right))
        case _ => proof.InvalidProofTactic("Only support goals of the form () |- left <= right")

    end apply

  end RestateWithAxioms


  val testp1 = Theorem(isO +: inU(z) |- (z <= z)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val testp4a = Theorem(isO +: inU(x, y) |- (x n y) <= x) {
    have(thesis) by RestateWithAxioms.apply
  }

  val testp5a = Theorem(isO +: inU(x, y) |- (x n y) <= y) {
    have(thesis) by RestateWithAxioms.apply
  }

  val testp7b = Theorem(isO +: inU(x) |- /(/(x)) <= x) {
    have(thesis) by RestateWithAxioms.apply
  }




/*
  val uni1, leq1, meet1, join1, not1 = variable

  extension (left: Term)
    def leq1(right: Term): Formula = in(pair(left, right), OrthologicWithAxiomsST.leq1)
    def meet1(right: Term): Term = app(OrthologicWithAxiomsST.meet1, pair(left, right))
    def join1(right: Term): Term = app(OrthologicWithAxiomsST.join1, pair(left, right))

  // AR needs inline ?
  def neg1(t: Term): Term = app(OrthologicWithAxiomsST.not1, t)

  val isO1 = isOrthollatice(uni1, leq1, meet1, join1, not1)

  def RestateWithAxioms1(using proof: library.Proof): F.Sequent => proof.ProofTacticJudgement =
    RestateWithAxioms.withParameters(uni1, leq1, meet1, join1, not1)

  val testp1 = Theorem(isO1 /\ (z ∈ uni1) |- (z leq1 z)) {
    have(thesis) by RestateWithAxioms1
  }

  val testp4a = Theorem(isO1 /\ (x ∈ uni1) /\ (y ∈ uni1) |- ((x meet1 y) leq1 x)) {
    have(thesis) by RestateWithAxioms1
  }

//  val test2 = Theorem(isO1 /\ (x ∈ uni1) /\ (y ∈ uni1) |- ((x meet1 y) leq1 x)) {
//    have(thesis) by RestateWithAxioms(uni1, leq1, meet1, join1, not1)
//  }
*/


end OrthologicWithAxiomsST