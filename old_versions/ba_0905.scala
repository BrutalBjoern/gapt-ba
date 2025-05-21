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
  ctx += Notation.Infix("+", Precedence.plusMinus)
  ctx += hoc"m: i>i"
  ctx += Notation.Infix("m", Precedence.plusMinus)
  ctx += hoc"*: i>i>i"
  ctx += Notation.Infix("*", Precedence.timesDiv)
  //ctx += hoc"M: i>(i>o)>i>o"

  // i > (i > o) > i > o
  //ctx += hof"(x ** A) = ( λy ∃a ( (A a) ∧ y = x*a ) )"
  //ctx += hof" ν(k,l) = ( λa ∃(n:i) a = k + n * l )"
  //ctx += hof" ν(x,A) = ( λy ∃(a:i) ( (A a) ∧ y = x*a ) )"
  ctx += Notation.Infix("**", Precedence.timesDiv)
  ctx += hof"x ** A = ( λy ∃(a:i) ( (A a) ∧ y = x*a ) )"

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
        Seq("extens" -> hof"((A = B) <-> !(z:i) (A z <-> B z))"),
        Seq("antisym" -> hof"!A!B (( A ⊆ B & B ⊆ A ) -> ( A = B ))")
    )
  ) {
  trivial
  }

  def subTransitivity = Lemma(
    Sequent() :+ ("trans" -> hof"!A!B!C ( ( A ⊆ B & B ⊆ C ) -> ( A ⊆ C ) )")
  ) {
    allR
    allR
    allR
    unfold("⊆") in "trans"
    decompose
    allL("trans_0_0",hov"x:i").forget
    allL("trans_0_1",hov"x:i").forget
    
  }

  def sumCompatibility = Lemma(
    Sequent(
      Seq("defsum" -> hof"!(A:set)!(B:set)!(C:set) (sum_set(A,B) = C <-> !(x:i) (el(x,C) <-> ?(y:i)?(z:i) (el(y,A) & el(z,B) & (y + z = x))))"),
      Seq("comp1" -> hof"!(A:set)!(B:set)!(C:set) (A ⊆ B -> sum_set(C,A) ⊆ sum_set(C,B))")
    ) 
  ){
    decompose
  }
  

  def multleftCompatibility = Lemma(
    Sequent(
      Seq("defmult" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))"),
      Seq("comp2" -> hof"!(A:set)!(B:set) (A ⊆ B -> !(x:i)(multleft_set(x,A) ⊆ multleft_set(x,B)))")
    ) 
  ){
    decompose
  }

  def multClosed = Lemma(
    Sequent(
      Seq("*closed" -> hof"!(x:i)!(y:i)?(z:i) (x * y = z)", 
          "defmultleft" -> hof"!(A:set)!(B:set)!(x:i) (multleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x * z = y)))"),
      Seq("R*closed" -> hof"!(x:i) multleft_set(x,R) ⊆ R")
    )
  ){
    decompose
  }

  def plusClosed = Lemma(
    Sequent(
      Seq("+closed" -> hof"!(x:i)!(y:i)?(z:i) (x + y = z)", 
          "defplusleft" -> hof"!(A:set)!(B:set)!(x:i) (plusleft_set(x, A) = B <-> !(y:i) (el(y,B) <-> ?(z:i) (el(z,A) & x + z = y)))"),
      Seq("R+closed" -> hof"!(x:i) plusleft_set(x,R) ⊆ R")
    )
  ){
    decompose
  }

  def setPlusClosed = Lemma(
    Sequent(
      Seq("+closed" -> hof"!(x:i)!(y:i)?(z:i) (x + y = z)", 
          "defsum" -> hof"!(A:set)!(B:set)!(C:set) (sum_set(A,B) = C <-> !(x:i) (el(x,C) <-> ?(y:i)?(z:i) (el(y,A) & el(z,B) & (y + z = x))))"),
      Seq("set+closed" -> hof"!(x:i) sum_set(R,R) ⊆ R")
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
    :+ ("inverse" -> hof"!(a:i)!(b:i) (?(x:i) ( (1 + (m a*b)) * x = 1 ) -> ?(y:i) ( (1 + (m b*a)) * y = 1 ))")
  ){
    decompose
  }

}

