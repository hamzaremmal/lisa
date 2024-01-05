package lisa.ol

trait OrthologicWithAxiomsMain extends lisa.prooflib.BasicMain: // extends lisa.prooflib.BasicMain:
  library: OrthologicWithAxiomsLibrary =>
  
  export automation.ElementInOrtholattice
  export automation.RestateWithAxioms

end OrthologicWithAxiomsMain
