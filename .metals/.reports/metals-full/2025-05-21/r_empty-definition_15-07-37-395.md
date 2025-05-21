error id: file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/gapt-ba/ba.scala:`<none>`.
file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/gapt-ba/ba.scala
empty definition using pc, found symbol in pc: `<none>`.
empty definition using semanticdb
empty definition using fallback
non-local guesses:
	 -gapt/expr/Notation.Infix.
	 -gapt/expr/Notation.Infix#
	 -gapt/expr/Notation.Infix().
	 -gapt/formats/babel/Notation.Infix.
	 -gapt/formats/babel/Notation.Infix#
	 -gapt/formats/babel/Notation.Infix().
	 -gapt/proofs/gaptic/Notation.Infix.
	 -gapt/proofs/gaptic/Notation.Infix#
	 -gapt/proofs/gaptic/Notation.Infix().
	 -Notation.Infix.
	 -Notation.Infix#
	 -Notation.Infix().
	 -scala/Predef.Notation.Infix.
	 -scala/Predef.Notation.Infix#
	 -scala/Predef.Notation.Infix().
offset: 477
uri: file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/gapt-ba/ba.scala
text:
```scala
import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object proof extends TacticsProof {
  ctx += Sort("i")

  ctx += Notation.Infix( "⊆", Precedence.infixRel)
  ctx += hof"(A ⊆ B) = (!(x:i) ((A x) -> (B x)))"

  ctx += Const("0", Ti)
  ctx += Const("1", Ti)
  ctx += hoc"+: i>i>i"
  ctx += Notation.Infi@@x("+", Precedence.plusMinus)
  ctx += hoc"m: i>i"
  ctx += Notation.Infix("m", Precedence.plusMinus)
  ctx += hoc"*: i>i>i"
  ctx += Notation.Infix("*", Precedence.timesDiv)
  //ctx += hof" ν(k,l) = ( λa ∃(n:i) a = k + n * l )"
  //ctx += hof" ν(x,A) = ( λy ∃(a:i) ( (A a) ∧ y = x*a ) )"
  ctx += Notation.Infix("**", Precedence.timesDiv)
  ctx += hof"x ** A = ( λy ∃(a:i) ( (A a) ∧ y = x*a ) )"
  ctx += Notation.Infix("++", Precedence.timesDiv)
  ctx += hof"x ++ A = ( λy ∃(a:i) ( (A a) ∧ y = x+a ) )"
  ctx += Notation.Infix("⊕", Precedence.plusMinus)
  ctx += hof"A ⊕ B = ( λy ∃(a:i) ∃(b:i) ( (A a) ∧ (B b) ∧ y = a+b ) )"

  ctx += hof"mulclosed R = ( !(x:i) !(y:i) ( R(x) -> R(y) -> R(x*y)))"

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


  def mulclosed_subset = Lemma(
    Sequent() :+ ("goal" -> hof"!(R:i>o) !(x:i) ( mulclosed R -> R(x) -> x ** R ⊆ R )")
  ) {
    decompose
    unfold("⊆") in "goal_1_1"
    decompose
    unfold("**") in "goal_1_1_0"
    decompose
    unfold("mulclosed") in "goal_0"
    allL("goal_0", hov"x:i", hov"a:i").forget
    eql("goal_1_1_0_1", "goal_0")
    prop
  }

  def subReflexivity = Lemma(Sequent() :+ ("ref" -> hof"A ⊆ A")) {
    unfold("⊆") in "ref"
    decompose
    trivial
  }

  def subAntisymmetry = Lemma(
    Sequent(
        Seq("extens" -> hof"!A!B ((A = B) <-> !(z:i) (A z <-> B z))"),
        Seq("antisym" -> hof"!A!B (( A ⊆ B & B ⊆ A ) -> ( A = B ))")
    )
  ) {
    allR("antisym",hov"A:i>o")
    allR("antisym",hov"B:i>o")
    decompose
    allL("extens",hov"A:i>o",hov"B:i>o").forget
    andL
    chain("extens_1")
    forget("extens_0","extens_1")
    decompose
    unfold("⊆") in ("antisym_0_0","antisym_0_1")
    andR left by {
      forget("antisym_0_1")
      allL("antisym_0_0",hov"z:i").forget
      trivial
    }
    forget("antisym_0_0")
    allL("antisym_0_1",hov"z:i").forget
    trivial
  }

  def subTransitivity = Lemma(
    Sequent() :+ ("trans" -> hof"!A!B!C ( ( A ⊆ B ∧ B ⊆ C ) -> ( A ⊆ C ) )")
  ) {
    allR
    allR
    allR
    unfold("⊆") in "trans"
    decompose
    allL("trans_0_0",hov"x:i").forget
    allL("trans_0_1",hov"x:i").forget
    impL("trans_0_0") left by {trivial}
    impL("trans_0_1") left by {trivial}
    trivial
  }

  def sumCompatibility = Lemma(
    Sequent() :+ ("comp+" -> hof"!A!B!C (A ⊆ B -> (C ⊕ A) ⊆ (C ⊕ B))")
  ){
    decompose
    unfold("⊕") in "comp+_1"
    unfold("⊆") in ("comp+_0","comp+_1")
    decompose
    allL("comp+_0",hov"b:i").forget
    impL("comp+_0") left by {trivial}
    exR(hov"a:i",hov"b:i").forget
    andR right by {trivial}
    andR left by{trivial}
    trivial
  }
  

  def multleftCompatibility = Lemma(
    Sequent() :+ ("comp*" -> hof"!A!B (A ⊆ B -> !x ( x ** A ⊆ x ** B))")
  ){
    decompose
    unfold("**") in "comp*_1"
    unfold("⊆") in ("comp*_0","comp*_1")
    decompose
    allL("comp*_0",hov"a:i").forget
    exR(hov"a:i").forget
    andR right by {trivial}
    impL("comp*_0") left by {trivial}
    trivial
  }

  def multClosed = Lemma(
    Sequent(
      Seq("R*closed" -> hof"!x!y?z ((R x ∧ R y) → (x * y = z ∧ R z))"), 
      Seq("left*closed" -> hof"!x (R x → x ** R ⊆ R)")
    )
  ){
    decompose
    unfold("**","⊆") in "left*closed_1"
    decompose
    allL("R*closed",hov"x:i",hov"a:i").forget
    exL("R*closed",hov"z:i")
    impL left by {
      andR left by {trivial}
      trivial
    }
    forget("left*closed_1_0_0","left*closed_0")
    eql("left*closed_1_0_1","R*closed")
    andL
    eql("R*closed_0","R*closed_2")
    trivial
  }

  def plusClosed = Lemma(
    Sequent(
      Seq("R+closed" -> hof"∀x∀y∃z ((R x ∧ R y) → (x + y = z ∧ R z))"),
      Seq("left+closed" -> hof"∀x (R x → x ++ R ⊆ R)")
    )
  ){
    decompose
    unfold("++","⊆") in "left+closed_1"
    decompose
    allL("R+closed",hov"x:i",hov"a:i").forget
    exL("R+closed",hov"z:i")
    impL left by {
      andR left by {trivial}
      trivial
    }
    forget("left+closed_1_0_0","left+closed_0")
    eql("left+closed_1_0_1","R+closed")
    andL
    eql("R+closed_0","R+closed_1")
    trivial
  }

  def setPlusClosed = Lemma(
    Sequent(
      Seq("R+closed" -> hof"∀x∀y∃z ((R x ∧ R y) → (x + y = z ∧ R z))"),
      Seq("set+closed" -> hof"!(x:i) R ⊕ R ⊆ R")
    )
  ){
    decompose
    unfold("⊕","⊆") in "set+closed"
    decompose
    allL("R+closed",hov"a:i",hov"b:i").forget
    exL
    eql("set+closed_0_1","R+closed")
    impL left by {
      andR left by{trivial}
      trivial
    }
    andL
    eql("R+closed_0","R+closed_1")
    trivial
  }

  def multleftAssoc = Lemma(
    Sequent(
        Seq("extens" -> hof"!A!B ((A = B) <-> !(z:i) (A z <-> B z))"),
        Seq("multsetassoc" -> hof"∀x∀y∀R x ** (y ** R) = (x * y) ** R")
    )
  ){
    unfold("**") in "multsetassoc"
    decompose
    allR
  }

  def inverse = Lemma(
    Sequent() :+ ("inverse" -> hof"!(a:i)!(b:i) (?(x:i) ( (1 + (m a*b)) * x = 1 ) -> ?(y:i) ( (1 + (m b*a)) * y = 1 ))")
  ){
    decompose
  }

}


```


#### Short summary: 

empty definition using pc, found symbol in pc: `<none>`.