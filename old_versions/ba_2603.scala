import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object proof extends TacticsProof {
  ctx += Sort("i")
  ctx += Sort("set")
  ctx += hoc"el: i>set>o"
  ctx += hoc"sub: set>set>o"

  val axioms = ("eqrefl" -> hof"!x x=x")
    +: ("eqsymm" -> hof"!(x:i)!y (x=y -> y=x)")
    +: ("eqtrans" -> hof"!(x:i)!y!z (x=y & y=z -> x=z)")
    +: ("extens" -> hof"!(A:set)!(B:set) ((A = B) <-> !(z:i) (el(z,A) <-> el(z,B)))")
    +: ("emptyset" -> hof"?(C:set)!(x:i) -el(x,C)")
    +: ("singleton" -> hof"!(a:i)?(A:set)!(x:i)(el(x,A) <-> (x = a))")
    +: ("union" -> hof"!(A:set)!(B:set)?(C:set)!(x:i) ( el(x,C) <-> (el(x,A) | el(x,B) ))")
    +: Sequent()

  ctx += Notation.Infix("<=", Precedence.infixRel)
  ctx += hof"(A <= B) = (!(x:i) (el(x,A) -> el(x,B)))"

  def subReflexivity = Lemma(Sequent() :+ ("ref" -> hof"!(A:set) A <= A")) {
    allR(hov"X:set")
    unfold("<=") in "ref"
    allR
    impR
    trivial
  }

  def subAntisymmetry = Lemma(
    Sequent(
        Seq("extens" -> hof"!(A:set)!(B:set) ((A = B) <-> !(z:i) (el(z,A) <-> el(z,B)))"),
        Seq("antisym" -> hof"!(A:set)!(B:set) ( ( A <= B & B <= A ) -> ( A = B ) )")
  )
   ) {
    allR
    allR
    unfold("<=") in "antisym"
    
  }

  def subTransitivity = Lemma(
    Sequent() :+ ("trans" -> hof"!(A:set)!(B:set)!(C:set) ( ( A <= B & B <= C ) -> ( A <= C ) )")
  ) {
    allR
    allR
    allR
    unfold("<=") in "trans"
    impR
  }

  ctx += hoc"0:i"
  ctx += Notation.Infix("+", Precedence.infixRel)
  ctx += hof"?(x:i) (x + 0) = x"
  ctx += hof"?(x:i)?(y:i) !(z:i) (x + y = z)"
  ctx += hof"?(x:i)?(y:i)?(z:i) ((x + y) + z) = (x + (y + z))"
  ctx += hof"?(x:i)!(y:i) (x + y) = 0"
  ctx += hof"?(x:i)?(y:i) (x + y = y + x)"

  ctx += hoc"1:i"
  ctx += Notation.Infix("*", Precedence.infixRel)
  ctx += hof"?(x:i) (x * 1) = x"
  ctx += hof"?(x:i)?(y:i) !(z:i) (x * y = z)"
  ctx += hof"?(x:i)?(y:i)?(z:i) ((x * y) * z) = (x * (y * z))"


}

