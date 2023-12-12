package lisa.maths

import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.orderings.PartialOrders.*

object OrthologicWithAxioms extends lisa.Main:

  private val o = variable

  private val S = variable
  private val leq = variable
  private val meet, join = variable
  private val neg2 = variable
  private val zero, one = variable
  
  val x, y, z = variable


//  val unaryOperation = DEF(S, meet) --> functionFrom(meet, S, S)
//  val binaryOperation = DEF(S, meet) --> functionFrom(meet, cartesianProduct(S, S), S)


  def neg2(t: Term): Term = app(OrthologicWithAxioms.neg2, x)
  extension (left: Term)
    def leq(right: Term): Formula = in(pair(left, right), OrthologicWithAxioms.leq)
    def meet(right: Term): Term = app(OrthologicWithAxioms.meet, pair(left, right))
    def join(right: Term): Term = app(OrthologicWithAxioms.join, pair(left, right))


  // TODO everywhere: x,y in S

  val p1 = ∀(x, in(x, S) ==> (x leq x))
  val p2 = ∀(x, in(x, S) ==> ∀(y, in(y, S) ==> ∀(z, in(z, S) ==>
    (((x leq y) /\ (y leq z)) ==> (x leq z))
  )))

  val p3 = (zero leq x) /\ (x leq one)

  val p4 = in(pair((x meet y), x), leq) /\ in(pair(x, (x join y)), leq)
  val p5 = in(pair((x meet y), y), leq) /\ in(pair(y, (x join y)), leq)

  val p6 = ((x leq y) /\ (x leq z) ==> (x leq (x meet z))) /\ ((x leq z) /\ (y leq z) ==> ((x join y) leq z))

  val p7 = (x leq neg2(neg2(x))) /\ (neg2(neg2(x)) leq x)
  val p8 = (x leq y) ==> (neg2(y) leq neg2(x))
  val p9 = ((x meet neg2(x)) leq zero) /\ (one leq (x join neg2(x)))

  val SxS = cartesianProduct(S, S)

  /**
   * Ortholattice --- `o` is an ortholattice on `x` if it is a
   * (S, leq, meet, join, neg) and
   * `r` is [[reflexive]], [[transitive]], [[]]
   * */
  val ortholattice = DEF(S, leq, meet, join, neg2) --> {
    relationBetween(leq, S, S)
      /\ p1 /\ p2
//      /\ functionFrom(meet, SxS, S)
//      /\ functionFrom(join, SxS, S)
//      /\ functionFrom(neg2, S, S)
//      /\ p3 /\ p4 /\ p5 /\ p6 /\ p7 /\ p8 /\ p9
  }


  val hyp = Theorem(ortholattice(S, leq, meet, join, neg2) /\ (x ∈ S) |- (x leq x)) {
    assume(ortholattice(S, leq, meet, join, neg2))

    have(p1) by Tautology.from(ortholattice.definition)
    thenHave(∀(x, in(x, S) ==> (x leq x))) by Restate
    thenHave((x ∈ S) |- (x leq x)) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }



end OrthologicWithAxioms
