package lisa.prooflib

trait BasicMain {
  library: Library =>

  private val realOutput: String => Unit = println

  /**
   * This specific implementation make sure that what is "shown" in theory files is only printed for the one we run, and not for the whole library.
   */
  def main(args: Array[String]): Unit = {
    realOutput(library.om.stringWriter.toString)
  }

}
