import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object proof extends TacticsProof {
  ctx += Sort("i")
  ctx += Sort("set")
  ctx += hoc"el: i>set>o"
  ctx += Notation.Infix("<=", Precedence.infixRel)
  ctx += hof"(A <= B) = (!(x:i) (el(x,A) -> el(x,B)))"

  ctx += Const("0", Ti)
  ctx += Const("1", Ti)
  ctx += hoc"+: i>i>i"
  ctx += Notation.Infix("+", Precedence.plusMinus)
  ctx += hoc"*: i>i>i"
  ctx += Notation.Infix("*", Precedence.timesDiv)

  ctx += hoc"sum_set: set>set>set"
  ctx += hoc"multleft_set: i>set>set"
  ctx += hoc"plusleft_set: i>set>set"


  val axioms = 
       ("eqrefl" -> hof"!x x=x")
    +: ("eqsymm" -> hof"!(x:i)!y (x=y -> y=x)")
    +: ("eqtrans" -> hof"!(x:i)!y!z (x=y & y=z -> x=z)")
    +: ("extens" -> hof"!(A:set)!(B:set) ((A = B) <-> !(z:i) (el(z,A) <-> el(z,B)))")
    +: ("emptyset" -> hof"?(C:set)!(x:i) -el(x,C)")
    +: ("singleton" -> hof"!(a:i)?(A:set)!(x:i)(el(x,A) <-> (x = a))")
    +: ("union" -> hof"!(A:set)!(B:set)?(C:set)!(x:i) ( el(x,C) <-> (el(x,A) | el(x,B) ))")
    +: Sequent()

  val Ringaxioms = 
       ("+neutral" -> hof"!(x:i) x + 0 = x")
    +: ("+closed" -> hof"!(x:i)!(y:i)?(z:i) (x + y = z)")
    +: ("+assoc" -> hof"!(x:i)!(y:i)!(z:i) ((x + y) + z) = (x + (y + z))")
    +: ("+inverse" -> hof"!(x:i)?(y:i) (x + y) = 0")
    +: ("+comm" -> hof"!(x:i)!(y:i) (x + y = y + x)")
    +: ("*neutral" -> hof"!(x:i) (x * 1) = x")
    +: ("*closed" -> hof"!(x:i)!(y:i)?(z:i) (x * y = z)")
    +: ("*assoc" -> hof"!(x:i)!(y:i)!(z:i) ((x * y) * z) = (x * (y * z))")
    +: Sequent()

  val Definitions =
       ("defmultleft" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))")
    +: ("defsum" -> hof"!(A:set)!(B:set)!(C:set) (sum_set(A,B) = C <-> !(x:i) (el(x,C) <-> ?(y:i)?(z:i) (el(y,A) & el(z,B) & (y + z = x))))")
    +: ("defplusleft" -> hof"!(A:set)!(B:set)!(x:i) (plusleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x + z = y)))")
    +: Sequent()


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
    decompose
    allL("extens", hov"A:set", hov"B:set").forget
    andL
    forget("extens_0")
    impL("extens_1") right by { trivial }
    forget("antisym_1")
    decompose
    andR left by {
      forget("antisym_0_1")
      unfold("<=") in "antisym_0_0"
      escargot
    }
    unfold("<=") in "antisym_0_1"
    escargot
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

  def sumCompatibility = Lemma(
    Sequent(
      Seq("defsum" -> hof"!(A:set)!(B:set)!(C:set) (sum_set(A,B) = C <-> !(x:i) (el(x,C) <-> ?(y:i)?(z:i) (el(y,A) & el(z,B) & (y + z = x))))"),
      Seq("comp1" -> hof"!(A:set)!(B:set)!(C:set) (A <= B -> sum_set(C,A) <= sum_set(C,B))")
    ) 
  ){
    decompose
  }
  

  def multleftCompatibility = Lemma(
    Sequent(
      Seq("defmult" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))"),
      Seq("comp2" -> hof"!(A:set)!(B:set) (A <= B -> !(x:i)(multleft_set(x,A) <= multleft_set(x,B)))")
    ) 
  ){
    decompose
  }

  def multClosed = Lemma(
    Sequent(
      Seq("*closed" -> hof"!(x:i)!(y:i)?(z:i) (x * y = z)", 
          "defmultleft" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))"),
      Seq("R*closed" -> hof"!(x:i) multleft_set(x,R) <= R")
    )
  ){
    decompose
  }

  def plusClosed = Lemma(
    Sequent(
      Seq("+closed" -> hof"!(x:i)!(y:i)?(z:i) (x + y = z)", 
          "defplusleft" -> hof"!(A:set)!(B:set)!(x:i) (plusleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x + z = y)))"),
      Seq("R+closed" -> hof"!(x:i) plusleft_set(x,R) <= R")
    )
  ){
    decompose
  }

  def setPlusClosed = Lemma(
    Sequent(
      Seq("+closed" -> hof"!(x:i)!(y:i)?(z:i) (x + y = z)", 
          "defsum" -> hof"!(A:set)!(B:set)!(C:set) (sum_set(A,B) = C <-> !(x:i) (el(x,C) <-> ?(y:i)?(z:i) (el(y,A) & el(z,B) & (y + z = x))))"),
      Seq("set+closed" -> hof"!(x:i) sum_set(R,R) <= R")
    )
  ){
    decompose
  }

  def multleftAssoc = Lemma(
    Sequent(
      Seq("defmult" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))"),
      Seq("multsetassoc" -> hof"!(x:i)!(y:i)!(R:set) (multleft_set(x,multleft_set(y,R)) = multleft_set(x*y,R))")
    )
  ){
    decompose
  }

  def inverse = Lemma(
    Sequent()
    :+ ("inverse" -> hof"!(a:i)!(b:i) (?(x:i) ( (1 - a*b) * x = 1 ) -> ?(y:i) ( (1 - b*a) * y = 1 ))")
  ){
    decompose
  }
}

