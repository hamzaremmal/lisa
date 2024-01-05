package lisa.ol
package tests

import lisa.SetTheoryLibrary.∈
import lisa.ol.OrthologicWithAxiomsLibrary.{n, not, u}

object ElementInOrtholatticeTest extends OrthologicWithAxiomsMain:

  val elemInOrtho1 = Theorem(ortholattice(U, <=, n, u, not, 0, 1) |- 0 ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(0)
  end elemInOrtho1

  val elemInOrtho2 = Theorem(ortholattice(U, <=, n, u, not, 0, 1) |- 1 ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(1)
  end elemInOrtho2

  val elemInOrtho3 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U) |- x ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x)
  end elemInOrtho3

  val elemInOrtho4 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U) |- !x ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x)
  end elemInOrtho4

  val elemInOrtho5 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n y)
  end elemInOrtho5

  val elemInOrtho6 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x u y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x u y)
  end elemInOrtho6

  val elemInOrtho7 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- !(x u y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!(x u y))
  end elemInOrtho7

  val elemInOrtho8 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- !(x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!(x n y))
  end elemInOrtho8

  val elemInOrtho9 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (!x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x n y)
  end elemInOrtho9

  val elemInOrtho10 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n !y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n !y)
  end elemInOrtho10

  val elemInOrtho11 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (!x n y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(!x n y)
  end elemInOrtho11

  val elemInOrtho12 = Theorem((ortholattice(U, <=, n, u, not, 0, 1), x ∈ U, y ∈ U) |- (x n !y) ∈ U):
    have(thesis) by ElementInOrtholattice.withParameters(x n !y)
  end elemInOrtho12

end ElementInOrtholatticeTest