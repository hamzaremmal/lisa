package lisa.ol

trait OrthologicWithAxiomsMain: // extends lisa.prooflib.BasicMain:
  library: OrthologicWithAxiomsLibrary =>
  
  export automation.ElementInOrtholattice
  export automation.RestateWithAxioms

  def main(args: Array[String]) =
    println(library.om.stringWriter.toString)
  end main

end OrthologicWithAxiomsMain
