package lisa.ol
package automation

import scala.collection.mutable

import lisa.maths.settheory.SetTheory.*
import lisa.fol.FOL.*
import lisa.prooflib.ProofTacticLib.ProofTactic

object RestateWithAxioms extends ProofTactic:

  object Singleton:
    def unapply(t: Term): Option[Term] = t match
      case unorderedPair(x1, x2) if x1 == x2 => Some(x1)
      case _ => None

  object Pair:
    def unapply(t: Term): Option[(Term, Term)] = t match
      case unorderedPair(unorderedPair(x1, y1), Singleton(x2)) if x1 == x2 => Some((x1, y1))
      case _ => None

  enum Annotated:
    case L(t: Term)
    case R(t: Term)
    case N
  import Annotated.*

  // AR
  val leq = OrthologicWithAxiomsLibrary.<=
  val meet = OrthologicWithAxiomsLibrary.n
  val join = OrthologicWithAxiomsLibrary.u
  val not0 = OrthologicWithAxiomsLibrary.not // RN

  var log = false

  object Leq:
    def unapply(t: Formula): Option[(Term, Term)] = t match
      case in(Pair(x, y), `leq`) => Some((x, y))
      case _ => None

  object Meet:
    def unapply(t: Term): Option[(Term, Term)] = t match
      case app(`meet`, Pair(x, y)) => Some((x, y))
      case _ => None

  object Join:
    def unapply(t: Term): Option[(Term, Term)] = t match
      case app(`join`, Pair(x, y)) => Some((x, y))
      case _ => None

  object Not:
    def unapply(t: Term): Option[Term] = t match
      case app(`not0`, x) => Some(x)
      case _ => None

  def apply(using lib: OrthologicWithAxiomsLibrary.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =
    import lib.{isO, inU, U, `0`, `1`}
    // TODO better error messages
    if bot.right.size != 1 then
      proof.InvalidProofTactic("Only support goals of the form ??? |- left <= right")
    else if !(bot.left contains isO) then
      proof.InvalidProofTactic("Only support goals of the form isO +: ... |- left <= right")
    else bot.right.head match
      //        case in(Pair(left, right), `leq`) =>
      case Leq(left, right) => // FIX
        //          val Leq(left, right) = bot.right.head

        val left1 = if left == `1` then N else L(left)
        val right1 = if right == `0` then N else R(right)
        /*
        (left, right) match
          case (`1`, `0`) | (`0`, `1`) => prove(N, N)
          case (`1`, r) => prove(N, R(r))
          case (r, `1`) =>
          case (l, `0`) =>
        */

        val termsInU = bot.left.collect { case in(x1, U) => x1 }

        val axioms = bot.left.collect {
          case t @ Leq(_, _) => t // TODO? check inU ?
          //            case Leq(`1`, `0`) => (N, N)
          //            case Leq(`1`, r) => (N, R(r))
          //            case Leq(l, `0`) => (L(l), N)
          //            case Leq(l, r) => (L(l), R(r))
          // AR!
        }
        if log then println(s"axioms: $axioms")

        withParameters(termsInU, axioms)(left1, right1)
      // TODO Weakening if bot.left contains more stuff

      case _ => proof.InvalidProofTactic("Only support goals of the form () |- left <= right")

  end apply

  // IMPROVE such that do not neet to write .apply
  // isOrthollatice(U, <=, n, u, not) |- left <= right
  def withParameters(using lib: OrthologicWithAxiomsLibrary.type, proof: lib.Proof)
                    //                      (termsInU: Set[Term], axioms: Set[(Annotated, Annotated)])
                    (termsInU: Set[Term], axioms: Set[Formula])
                    (left: Annotated, right: Annotated): proof.ProofTacticJudgement =
    import lib.{isO, inU, U, `0`, `1`, assume, have, andThen, lastStep, x, y, z}
    val premises = isO +: inU(termsInU.toSeq*)

    val axFormulas: Set[Term] = axioms
      //        .flatMap(Set(_, _)).collect { case L(x) => x case R(x) => x }
      .flatMap { case Leq(l, r) => Set(l, r) }.filterNot(Set(`0`, `1`)) // AR not exhaustive (flatMap)

    val chacheInU = mutable.Map[Term, Any]() // TODO!

    def provedInU(using proof: lib.Proof)(t: Term): Boolean = proveInU(t).isValid

    def proveInU(using proof: lib.Proof)(t: Term): proof.ProofTacticJudgement =
      val p = assume(premises*)
      t match
        case `1` | `0` => ???
        case x1 if termsInU contains x1 =>
          TacticSubproof:
            have(x1 ∈ U) by Weakening(p)

        case Not(x1) =>
          proveInU(x1) andThen2 { lastStep =>
            have(!x1 ∈ U) by Cut(lastStep, lib.negationIsClosed of (x := x1))
          }

        case Meet(x1, y1) =>
          proveInU(x1) andThen { s1 =>
            proveInU(y1) andThen2 { s2 =>
              have(x1 ∈ U /\ y1 ∈ U) by RightAnd(s1, s2)
              have((x1 n y1) ∈ U) by Cut(lastStep, lib.meetIsClosed of(x := x1, y := y1))
            }
          }

        case Join(x1, y1) =>
          proveInU(x1) andThen { s1 =>
            proveInU(y1) andThen2 { s2 =>
              have(x1 ∈ U /\ y1 ∈ U) by RightAnd(s1, s2)
              have((x1 u y1) ∈ U) by Cut(lastStep, lib.joinIsClosed of(x := x1, y := y1))
            }
          }

        case other => proof.InvalidProofTactic(s"Could not prove $other ∈ $U") // RN?

    end proveInU

    extension (a: Annotated)
      def pos1: Term = a match
        case L(t) => t case R(t) => !t case N => `1`
      def pos2: Term = a match
        case L(t) => !t case R(t) => t case N => `0`

    // MV to proveNoC start a vals

    val cache = mutable.Map[(Annotated, Annotated), Any]()

    var ident = 0

    def prove(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement =
      cache.get(gamma, delta) match
        case Some(cachedSamePath: proof.ProofTacticJudgement) =>
          cachedSamePath
        case Some(r) if r.isInstanceOf[proof.InvalidProofTactic] =>
          r.asInstanceOf[proof.ProofTacticJudgement]
        // NOTE works to avoid cycles but doesn't reuse a ValidProofTactic with different path
        case _ =>
          if log then println(" " * ident + s"== starting prove($gamma, $delta)")
          ident += 1

          cache.addOne((gamma, delta), proof.InvalidProofTactic(s"Starting prove($gamma, $delta)"))
          val res: proof.ProofTacticJudgement = proveNoC(gamma, delta)
          res match
            case proof.ValidProofTactic(bot, _, _) =>
              val expected = gamma.pos1 <= delta.pos2
              assert(bot.right.size == 1, s"${bot.right - expected}")
              assert(bot.right.head == expected, s"\n${bot.right.head} \n!= \n$expected \n$gamma $delta")
            case _ =>
          cache.addOne((gamma, delta), res)

          ident -= 1
          if log then println(" " * ident + s"== ending prove($gamma, $delta) with ${res.isValid}")
          res
    end prove

    def proved(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): Boolean = prove(gamma, delta).isValid

    // IMPROVE by
    //  - rm nesting of subproofs
    //  - rm as mush as can premises of the form isInU

    // CHECK ordering importance

    /*
    L(x) delta --> x <= I(delta)
    gamma R(x) --> I(gamma) <= x

    AR assuming never
    N L
    R N
    * */

    extension (s: Sequent) // RM
      def toString2 = "\nleft:" + s.left.map(f => s"\n\t$f") + "\nright:" + s.right.map(f => s"\n\t$f")

    // prove isO /\ ... in universe |- gamma delta
    def proveNoC(using proof: lib.Proof)(gamma: Annotated, delta: Annotated): proof.ProofTacticJudgement = TacticSubproof:
      assume(isO +: inU(termsInU.toSeq*) concat axioms *) // RN

      val gammaF = gamma.pos1 // AR use more
      val deltaF = delta.pos2 // AR use more
      val goalRight = gammaF <= deltaF

      (gamma, delta) match

        case (L(x1), R(y1)) if x1 == y1 =>
          have(inU(x1) |- (x1 <= y1)) by Weakening(lib.hyp of (x := x1))

        //            // NOTE code below is for dicharging merged into main tactic
        //            val s1 = have(proveInU(x1))
        //            have(x1 ∈ U |- x1 <= y1) by Weakening(hyp of (x := x1))
        //            andThen(Discharge(s1))
        ////            have(x1 <= y1) by Cut(s1, hyp of (x := x1))

        // Ax
        case _ if axioms contains (gammaF <= deltaF) =>
          have(gammaF <= deltaF) by RewriteTrue

        /** Deconstructing L **/

        // Contraction
        case (L(x1), N) if proved(L(x1), L(x1)) =>
          val s1 = have(prove(L(x1), L(x1)))
          have(s1.bot.left |- x1 <= `0`) by Cut(s1, lib.contraction1 of (x := x1))

        // Weaken
        case (L(x1), delta) if proved(L(x1), N) =>
          val s1 = have(prove(L(x1), N))
          have(s1.bot.left ++ inU(x1, deltaF) |- x1 <= deltaF) by
            Cut.withParameters(x1 <= `0`)(s1, lib.weaken1 of (x := x1, y := deltaF))

        // LeftNot
        case (L(Not(x1)), delta) if proved(R(x1), delta) =>
          have(prove(R(x1), delta))
        //          case (L(Not(x1)), delta) if proved(delta, R(x1)) && false => ??? // RM

        // LeftAnd
        case (L(Meet(x1, y1)), delta) if proved(L(x1), delta) =>
          val s1 = have(prove(L(x1), delta))
          have(s1.bot.left ++ inU(x1, y1, deltaF) |- (x1 n y1) <= deltaF) by Cut(s1, lib.leftAnd1 of (x := x1, y := y1, z := deltaF))
        case (L(Meet(x1, y1)), delta) if proved(L(y1), delta) =>
          val s1 = have(prove(L(y1), delta))
          have(s1.bot.left ++ inU(x1, y1, deltaF) |- (x1 n y1) <= deltaF) by Cut(s1, lib.leftAnd2 of (x := x1, y := y1, z := deltaF))

        // LeftOr
        case (L(Join(x1, y1)), delta) if proved(L(x1), delta) && proved(L(y1), delta) =>
          val s1 = have(prove(L(x1), delta))
          val s2 = have(prove(L(y1), delta))
          have(s1.bot.left ++ s2.bot.left |- (x1 u y1) <= deltaF) by
            Tautology.from(s1, s2, lib.leftOr of (x := x1, y := y1, z := deltaF)) // IMPROVE use Cut

        case (gamma, L(x1)) if proved(L(x1), gamma) =>
          val s1 = have(prove(L(x1), gamma)) // x1 <= gamma.pos2
          gamma match
            case L(y1) => // s1: x1 <= !y1
              have(s1.bot.left ++ inU(x1, y1) |- y1 <= !x1) by Cut(s1, lib.commutLL of (x := x1, y := y1))
            //                have(s1.bot.left ++ inU(!y1) |- y1 <= !x1) by Cut(s1, commutLL of (x := x1, y := y1))
            case R(y1) => // s1: x1 <= y1
              have(s1.bot.left |- !y1 <= !x1) by Cut(s1, lib.commutRL of (x := x1, y := y1))
            case N => // s1: x1 <= 0
              ??? // AR can happen ?

        /** Deconstructing R **/

        // Contraction
        case (N, R(x1)) if proved(R(x1), R(x1)) =>
          val s1 = have(prove(R(x1), R(x1)))
          have(s1.bot.left |- `1` <= x1) by Cut(s1, lib.contraction2 of (x := x1))

        // Weaken
        case (gamma, R(x1)) if proved(N, R(x1)) =>
          val s1 = have(prove(N, R(x1)))
          assert(s1.bot.right.head == `1` <= x1)

          have(s1.bot.left ++ inU(gammaF, x1) |- gammaF <= x1) by
            //              Cut(s1, weaken2 of (x := gammaF, y := x1))
            Cut.withParameters(`1` <= x1)(s1, lib.weaken2 of (x := gammaF, y := x1)) // FIX

        // RightNot
        case (gamma, R(Not(x1))) if proved(gamma, L(x1)) =>
          have(prove(gamma, L(x1)))

        // RightAnd
        case (gamma, R(Meet(x1, y1))) if proved(gamma, R(x1)) && proved(gamma, R(x1)) =>
          val s1 = have(prove(gamma, R(x1)))
          val s2 = have(prove(gamma, R(y1)))
          have(s1.bot.left ++ s2.bot.left |- gammaF <= (x1 n y1)) by
            Tautology.from(s1, s2, lib.rightAnd of(x := gammaF, y := x1, z := y1)) // IMPROVE by using Cut

        // RightOr
        case (gamma, R(Join(x1, y1))) if proved(gamma, R(x1)) =>
          val s1 = have(prove(gamma, R(x1)))
          have(s1.bot.left ++ inU(gammaF, x1, y1) |- gammaF <= (x1 u y1)) by Cut(s1, lib.rightOr1 of (x := gammaF, y := x1, z := y1))
        case (gamma, R(Join(x1, y1))) if proved(gamma, R(y1)) =>
          val s1 = have(prove(gamma, R(y1)))
          have(s1.bot.left ++ inU(gammaF, x1, y1) |- gammaF <= (x1 u y1)) by Cut(s1, lib.rightOr2 of (x := gammaF, y := x1, z := y1))

        case (R(x1), delta) if proved(delta, R(x1)) =>
          val s1 = have(prove(delta, R(x1))) // delta.pos1 <= x1
          delta match
            case L(y1) => // s1: y1 <= x1
              have(s1.bot.left |- !x1 <= !y1) by Cut(s1, lib.commutRL of(x := y1, y := x1))
            case R(y1) => // s1: !y1 <= x1
              val s2 = lib.commutRR of(x := y1, y := x1)
              have(s1.bot.left ++ inU(x1) |- !x1 <= y1) by Cut(s1, s2) // IMRPOVE rm in(x1)
            case N => // s1: 1 <= x1
              ??? // AR can happen ?

        // AxCut IMPROVE perf ! TODO
        case (gamma, delta) if axFormulas.exists(x1 => proved(gamma, R(x1)) && proved(L(x1), delta)) =>
          LazyList.from(axFormulas)
            .map { x1 => (x1, (prove(gamma, R(x1)), prove(L(x1), delta))) }
            //              .collectFirst { case (x1, (s1: proof.ValidProofTactic, s2: proof.ValidProofTactic)) => // FIX
            .collectFirst { case (x1, (s1, s2)) if s1.isValid && s2.isValid =>

              val prem = s1.asInstanceOf[proof.ValidProofTactic].bot.left ++ s2.asInstanceOf[proof.ValidProofTactic].bot.left
              val s3 = have(prem |- (gammaF <= x1) /\ (x1 <= deltaF)) by RightAnd(have(s1), have(s2))
              val s4 = lib.cut of (x := gammaF, y := x1, z := deltaF)
              val goal: Sequent = prem ++ inU(gammaF, x1, deltaF) |- gammaF <= deltaF
              //                Cut.apply(s3, s4)(goal)
              have(goal) by Cut.withParameters((gammaF <= x1) /\ (x1 <= deltaF))(s3, s4)
              //                have(goal) by Cut(s3, s4)

            }.get

        // Ax REVIEW needed !?
        case _ if axioms contains (delta.pos1 <= gamma.pos2) => ???

        case (gamma, delta) => return proof.InvalidProofTactic(s"No rules applied to $gamma, $delta") // RN?

    end proveNoC

    prove(left, right) andThen2 { s0 =>

      val toDischarge = s0.bot.left.collect {
        case in(x1, `U`) if !termsInU.contains(x1) => x1
      }

      if toDischarge.isEmpty then
        have(s0.bot) by Tautology.from(s0) // FIX
      else
        val fs = toDischarge.toSeq.map { xi => have(proveInU(xi)) }
        have(s0.bot) by Tautology.from(s0) // FIX
        andThen(Discharge(fs *))
    }

  end withParameters

end RestateWithAxioms