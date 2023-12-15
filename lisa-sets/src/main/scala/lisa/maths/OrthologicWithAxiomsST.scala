package lisa.maths

import lisa.maths.settheory.SetTheory.*
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.fol.FOL as F
import lisa.prooflib.Library

object OrthologicWithAxiomsST extends lisa.Main:

  private val o = variable

  private val S = variable
  private val leq = variable
  private val meet, join = variable
  private val neg2 = variable
  private val zero, one = variable
  
  val x, y, z = variable


  def neg2(t: Term): Term = app(OrthologicWithAxiomsST.neg2, x)
  extension (left: Term)
    def leq(right: Term): Formula = in(pair(left, right), OrthologicWithAxiomsST.leq)
    def meet(right: Term): Term = app(OrthologicWithAxiomsST.meet, pair(left, right))
    def join(right: Term): Term = app(OrthologicWithAxiomsST.join, pair(left, right))


  // TODO everywhere: x,y in S
  // TODO as defs ?

  val reflexive2: ConstantPredicateLabel[2] = DEF(leq, S) -->
    relationBetween(leq, S, S) /\ ∀(x, (x ∈ S) ==> (x leq x))

  val transitive2: ConstantPredicateLabel[2] = DEF(leq, S) -->
    relationBetween(leq, S, S) /\ ∀(x, ∀(y, ∀(z, (((x leq y) /\ (y leq z)) ==> (x leq z)))))

  val p3 = (zero leq x) /\ (x leq one)
  val p4 = in(pair((x meet y), x), leq) /\ in(pair(x, (x join y)), leq)
  val p5 = in(pair((x meet y), y), leq) /\ in(pair(y, (x join y)), leq)
  val p6 = ((x leq y) /\ (x leq z) ==> (x leq (x meet z))) /\ ((x leq z) /\ (y leq z) ==> ((x join y) leq z))
  val p7 = (x leq neg2(neg2(x))) /\ (neg2(neg2(x)) leq x)
  val p8 = (x leq y) ==> (neg2(y) leq neg2(x))
  val p9 = ((x meet neg2(x)) leq zero) /\ (one leq (x join neg2(x)))

  val SxS = cartesianProduct(S, S)

  val ortholattice = DEF(S, leq, meet, join, neg2) --> {
    relationBetween(leq, S, S)
      /\ reflexive2(leq, S) /\ transitive2(leq, S)
//      /\ functionFrom(meet, SxS, S)
//      /\ functionFrom(join, SxS, S)
//      /\ functionFrom(neg2, S, S)
//      /\ p3 /\ p4 /\ p5 /\ p6 /\ p7 /\ p8 /\ p9
  }

  /**
   * (S, (leq, (meet, (join, neg))))
   * */
  val orthollatice2 = DEF(o) --> {
    val (S, o2) = (firstInPair(o), secondInPair(o))
    val (leq, o3) = (firstInPair(o2), secondInPair(o2))
    val (meet, o4) = (firstInPair(o3), secondInPair(o3))
    val (join, neg) = (firstInPair(o4), secondInPair(o4))
    ortholattice(S, leq, meet, join, neg)
  }


  val hyp = Theorem(ortholattice(S, leq, meet, join, neg2) /\ (x ∈ S) |- (x leq x)) {
    assume(ortholattice(S, leq, meet, join, neg2))
    have(∀(x, (x ∈ S) ==> (x leq x))) by Tautology.from(ortholattice.definition, reflexive2.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  // AR why can not remove (x ∈ S) /\ (y ∈ S) /\ (z ∈ S)
  val cut = Theorem(ortholattice(S, leq, meet, join, neg2) /\ (x ∈ S) /\ (y ∈ S) /\ (z ∈ S) /\
    (x leq y) /\ (y leq z) |- (x leq z)
  ) {
    assume(ortholattice(S, leq, meet, join, neg2) /\ (x ∈ S) /\ (y ∈ S) /\ (z ∈ S))
    have(∀(x, ∀(y, ∀(z, (((x leq y) /\ (y leq z)) ==> (x leq z)))))) by Tautology.from(ortholattice.definition, transitive2.definition)
    thenHave(((x leq y) /\ (y leq z)) ==> (x leq z)) by InstantiateForall(x, y, z)
    thenHave(thesis) by Restate
  }

  val weaken1 = Theorem(ortholattice(S, leq, meet, join, neg2) /\ (x leq zero) |- (x leq y)) {
    sorry
  }

  object RestateWithAxioms extends ProofTactic:

    def solve(using proof: Proof)
             (o: Term, isOrtholattice: proof.Fact)
             (axioms: Set[?])
             (bot: Sequent): proof.ProofTacticJudgement =
      given lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

      val isOrtholatticeSeq = proof.getSequent(isOrtholattice)
      val isOrtholatticeFormula: Formula = orthollatice2(o)

      val leq: Term = ??? // get leq from o

      if !F.contains(isOrtholatticeSeq.right, isOrtholatticeFormula) then
        proof.InvalidProofTactic(s"TODO") // TODO

      else if bot.left.nonEmpty || bot.right.size != 1 then
        proof.InvalidProofTactic("Can only be applied to solve goals of the form TODO") // TODO

      else TacticSubproof: // REVIEW what this does exactly
        val goal: F.Formula = bot.right.head

        val (left: Term, right: Term) = goal match
          case AppliedPredicate(`in`, Seq(hopefullyPair, `leq`)) =>
            hopefullyPair match
              case AppliedPredicate(`unorderedPair`, Seq(
                AppliedPredicate(`unorderedPair`, Seq(a11, a12)),
                AppliedPredicate(`unorderedPair`, Seq(a21, a22))
              )) => // FIX we are clearly using the odering from the implementation of pair here
                if !(a21 == a22) then proof.InvalidProofTactic("???")
                else a21 match
                  case `a11` => (a12, a21)
                  case `a12` => (a11, a21)
        ???
    end solve

  end RestateWithAxioms

end OrthologicWithAxiomsST

