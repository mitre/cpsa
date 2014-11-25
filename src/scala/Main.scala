package cpsaextras

import java.io._
import java.util.ResourceBundle;

object Main {

  /**
   * @param args the command line arguments
   */
  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println("Usage: cpsaextras INPUT")
      println(getVersion())
    }
    else {
      val in = new BufferedReader(new FileReader(args(0)))
      val sr = new SExprReader(args(0), in)
      val out = new PrintWriter(System.out)
      while (true) {
	val x = sr.read()
	if (x == null) {
	  out.close()
	  return
	}
	Printer.pp(out, 80, 2, x)
	out.println()
	out.println()
      }
    }
  }

  private var resources: ResourceBundle = null

  private val VERSION_RESOURCES = "cpsaextras/version"

  /**
   * Get program name and a version number from a resource.
   */
  def getVersion() = {
    if (resources == null)
      resources = ResourceBundle.getBundle(VERSION_RESOURCES)
    val program = resources.getString("program")
    val version = resources.getString("version")
    program + " " + version
  }
}
