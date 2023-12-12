package lisa.ol

import lisa.prooflib.BasicMain

/**
 * ???
 * @author Hamza REMMAL (hamza.remmal@epfl.ch)
 */
trait Main extends BasicMain with OrthologicLibrary:

  export automation.Axiom
  export automation.Cut
  export automation.Hypothesis
  export automation.Instantiate
  export automation.LeftAnd
  export automation.LeftNot
  export automation.LeftOr
  export automation.RightAnd
  export automation.RightNot
  export automation.RightOr
  export automation.Substitution
  export automation.Tautology
  export automation.Weaken
