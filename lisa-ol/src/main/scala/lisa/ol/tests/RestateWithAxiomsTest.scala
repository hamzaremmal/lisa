package lisa.ol
package tests

object RestateWithAxiomsTest extends OrthologicWithAxiomsMain with OrthologicWithAxiomsLibrary:

  // ================================ CAN IT PROVE THE AXIOMS ? ===================================

  val proveP1 = Theorem((isO, x ∈ U) |- x <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP1

  val proveP2 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= y, y <= z) |- x <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP2

  val proveP3A = Theorem((isO, x ∈ U) |- 0 <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP3A

  val proveP3B = Theorem((isO, x ∈ U) |- x <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveP3B

  val proveP4A = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP4A

  val proveP4B = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP4B

  val proveP5A = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= y):
    have(thesis) by RestateWithAxioms.apply
  end proveP5A

  val proveP5B = Theorem((isO, x ∈ U, y ∈ U) |- y <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP5B

  val proveP6A = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= y, x <= z) |- x <= (y n z)):
    have(thesis) by RestateWithAxioms.apply
  end proveP6A

  val proveP6B = Theorem((isO, x ∈ U, y ∈ U, z ∈ U, x <= z, y <= z) |- (x u y) <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP6B

  val proveP7A = Theorem((isO, x ∈ U) |- x <= !(!x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP7A

  val proveP7B = Theorem((isO, x ∈ U) |- !(!x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP7B

  val proveP8 = Theorem((isO, x ∈ U, y ∈ U,  x <= y) |- !y <= !x):
    have(thesis) by RestateWithAxioms.apply
  end proveP8

  val proveP9A = Theorem((isO, x ∈ U) |- (x n !x) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveP9A

  val proveP9B = Theorem((isO, x ∈ U) |- 1 <= (x u !x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP9B

  // ================================== CAN IT DO REWRITES ? ======================================

  // == ALL SORT OF REWRITES OF P1

  val proveRewriteP1_1 = Theorem((isO, z ∈ U) |- z <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_1

  val proveRewriteP1_2 = Theorem((isO, z ∈ U) |- !z <= !z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_2

  val proveRewriteP1_3 = Theorem((isO, x ∈ U, y ∈ U) |- (x u y) <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_3

  val proveRewriteP1_4 = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) <= (x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_4

  val proveRewriteP1_5 = Theorem((isO, x ∈ U, y ∈ U) |- !(x u y) <= !(x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_5

  val proveRewriteP1_6 = Theorem((isO, x ∈ U, y ∈ U) |- !(x n y) <= !(x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_6

  // == ALL SORT OF REWRITES OF P2

  // TODO

  // ALL SORT OF REWRITES OF P3A

  val proveRewriteP3A_1 = Theorem((isO, a ∈ U) |- 0 <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_1

  val proveRewriteP3A_2 = Theorem((isO, a ∈ U) |- 0 <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_2

  val proveRewriteP3A_3 = Theorem((isO, a ∈ U, b ∈ U) |- 0 <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_3

  val proveRewriteP3A_4 = Theorem((isO, a ∈ U, b ∈ U) |- 0 <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3A_4

  // == ALL SORT OF REWRITES OF P3B

  val proveRewriteP3B_1 = Theorem((isO, a ∈ U) |- a <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_1

  val proveRewriteP3B_2 = Theorem((isO, a ∈ U) |- !a <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_2

  val proveRewriteP3B_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_3

  val proveRewriteP3B_4 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP3B_4

  // == ALL SORT OF REWRITES OF P4A

  val proveRewriteP4A_1 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_1

  val proveRewriteP4A_2 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n b) <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_2

  val proveRewriteP4A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a n !b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_3

  val proveRewriteP4A_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) n c) <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_4

  val proveRewriteP4A_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b u c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_5

  val proveRewriteP4A_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_6

  val proveRewriteP4A_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_7

  // == ALL SORT OF REWRITES OF P4B

  val proveRewriteP4B_1 = Theorem((isO, a ∈ U, b ∈ U) |- a <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_1

  val proveRewriteP4B_2 = Theorem((isO, a ∈ U, b ∈ U) |- !a <= (!a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_2

  val proveRewriteP4B_3 = Theorem((isO, a ∈ U, b ∈ U) |- a <= (a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_3

  val proveRewriteP4B_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a u b) <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_4

  val proveRewriteP4B_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- a <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_5

  val proveRewriteP4B_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n b) <= ((a n b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_6

  val proveRewriteP4B_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- a <= (a u (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4B_7

  // == ALL SORT OF REWRITES OF P5A

  val proveRewriteP5A_1 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_1

  val proveRewriteP5A_2 = Theorem((isO, a ∈ U, b ∈ U) |- (a n !b) <= !b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_2

  val proveRewriteP5A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n b) <= b):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_3

  val proveRewriteP5A_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b u c)) <= (b u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_4

  val proveRewriteP5A_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) n c) <= c):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_5

  val proveRewriteP5A_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= (b n c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_6

  val proveRewriteP5A_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= c):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5A_7

  // == ALL SORT OF REWRITES OF P5B

  val proveRewriteP5B_1 = Theorem((isO, a ∈ U, b ∈ U) |- b <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_1

  val proveRewriteP5B_2 = Theorem((isO, a ∈ U, b ∈ U) |- !b <= (a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_2

  val proveRewriteP5B_3 = Theorem((isO, a ∈ U, b ∈ U) |- b <= (!a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_3

  val proveRewriteP5B_4 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (b u c) <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_4

  val proveRewriteP5B_5 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- c <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_5

  val proveRewriteP5B_6 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (b n c) <= (a u (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_6

  val proveRewriteP5B_7 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- c <= ((a n b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP5B_7

  // == ALL SORT OF REWRITES OF P6A

  // TODO

  // == ALL SORT OF REWRITES OF P6B

  // TODO

  // == ALL SORT OF REWRITES OF P7A

  val proveRewriteP7A_1 = Theorem((isO, a ∈ U) |- a <= !(!a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_1

  val proveRewriteP7A_2 = Theorem((isO, a ∈ U) |- !a <= !(!(!a))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_2

  val proveRewriteP7A_3 = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= !(!(a u b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_3

  val proveRewriteP7A_4 = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= !(!(a n b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_4

  // == ALL SORT OF REWRITES OF P7B

  val proveRewriteP7B_1 = Theorem((isO, a ∈ U) |- !(!a) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_1

  val proveRewriteP7B_2 = Theorem((isO, a ∈ U) |- !(!(!a)) <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_2

  val proveRewriteP7B_3 = Theorem((isO, a ∈ U, b ∈ U) |- !(!(a u b)) <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_3

  val proveRewriteP7B_4 = Theorem((isO, a ∈ U, b ∈ U) |- !(!(a n b)) <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7B_4

  // == ALL SORT OF REWRITES OF P8

  // TODO: ADD TESTS

  // == ALL SORT OF REWRITES OF P9A

  val proveRewriteP9A_1 = Theorem((isO, a ∈ U) |- (a n !a) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_1

  val proveRewriteP9A_2 = Theorem((isO, a ∈ U) |- (!a n !(!a)) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_2

  // NOTE: SIMPLIFY DOUBLE NEGATION IN `proveRewriteP9A_2`
  val proveRewriteP9A_3 = Theorem((isO, a ∈ U) |- (!a n a) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_3

  val proveRewriteP9A_4 = Theorem((isO, a ∈ U, b ∈ U) |- ((a u b) n !((a u b))) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_4

  val proveRewriteP9A_5 = Theorem((isO, a ∈ U, b ∈ U) |- ((a n b) n !((a n b))) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9A_5

  // == ALL SORT OF REWRITES OF P9B

  val proveRewriteP9B_1 = Theorem((isO, a ∈ U) |- 1 <= (a u !a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_1

  val proveRewriteP9B_2 = Theorem((isO, a ∈ U) |- 1 <= (!a u !(!a))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_2

  // NOTE: SIMPLIFY DOUBLE NEGATION IN `proveRewriteP9B_2`
  val proveRewriteP9B_3 = Theorem((isO, a ∈ U) |- 1 <= (!a u a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_3

  val proveRewriteP9B_4 = Theorem((isO, a ∈ U, b ∈ U) |- 1 <= ((a u b) u !(a u b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_4

  val proveRewriteP9B_5 = Theorem((isO, a ∈ U, b ∈ U) |- 1 <= ((a n b) u !(a n b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP9B_5

  // =================================== NON-TRIVIAL TESTS ========================================

  // == associativity

  val meetIsAssociative_1 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= ((a n b) n c)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_1

  val meetIsAssociative_2 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_2

  val joinIsAssociative_1 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- (a u (b u c)) <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_1

  val joinIsAssociative_2 = Theorem((isO, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) u c) <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_2

  // == commutativity

  val meetIsCommutative = Theorem((isO, a ∈ U, b ∈ U) |- (a n b) <= (b n a)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsCommutative

  val joinIsCommutative = Theorem((isO, a ∈ U, b ∈ U) |- (a u b) <= (b u a)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsCommutative

  // == De Morgan's laws

  val DeMorganLaw_1 = Theorem((isO, a ∈ U, b ∈ U) |- !(a u b) <= (!a n !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_1

  val DeMorganLaw_2 = Theorem((isO, a ∈ U, b ∈ U) |- (!a n !b) <= !(a u b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_2

  val DeMorganLaw_3 = Theorem((isO, a ∈ U, b ∈ U) |- !(a n b) <= (!a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_3

  val DeMorganLaw_4 = Theorem((isO, a ∈ U, b ∈ U) |- (!a u !b) <= !(a n b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_4

  // == idempotency

  val joinIsIdempotent_1 = Theorem((isO, x ∈ U) |- (x u x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_1

  val joinIsIdempotent_2 = Theorem((isO, x ∈ U) |- x <= (x u x)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_2

  val meetIsIdempotent_1 = Theorem((isO, x ∈ U) |- (x n x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_1

  val meetIsIdempotent_2 = Theorem((isO, x ∈ U) |- x <= (x n x)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_2

  // == absorption

  val absorption_1 = Theorem((isO, x ∈ U, y ∈ U) |- (x u (x n y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_1

  val absorption_2 = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x u (x n y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_2

  val absorption_3 = Theorem((isO, x ∈ U, y ∈ U) |- (x n (x u y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_3

  val absorption_4 = Theorem((isO, x ∈ U, y ∈ U) |- x <= (x n (x u y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_4

  // == from paper

  val fromPaper = Theorem((isO, x ∈ U, y ∈ U, 1 <= (x n (!x u y))) |- 1 <= y) :
    have(thesis) by RestateWithAxioms.apply
  end fromPaper

end RestateWithAxiomsTest