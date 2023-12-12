package lisa.ol

import lisa.kernel.proof.SequentCalculus.Sequent as KernelSequent

trait Sequents {

  case class Sequent(left: Set[?], right: Set[?]):
    require(left.size + right.size <= 2)
    def underlying: KernelSequent = ??? // KernelSequent(left.map(_.underlying), right.map(_.underlying))

}
