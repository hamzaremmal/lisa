package lisa

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends lisa.prooflib.BasicMain {
  library: SetTheoryLibrary =>
  import library.*

  export lisa.fol.FOL.{*, given}
  export lisa.prooflib.BasicStepTactic.*
  export lisa.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau

  knownDefs.update(emptySet, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(union, Some(unionAxiom))
  knownDefs.update(powerSet, Some(powerAxiom))
  knownDefs.update(subset, Some(subsetAxiom))

}
