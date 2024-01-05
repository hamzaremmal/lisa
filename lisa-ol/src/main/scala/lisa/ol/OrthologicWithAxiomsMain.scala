package lisa.ol

trait OrthologicWithAxiomsMain extends lisa.prooflib.BasicMain:

  export lisa.fol.FOL.{*, given}
  export OrthologicWithAxiomsLibrary.{*, given}
  export automation.ElementInOrtholattice

end OrthologicWithAxiomsMain
