import at.logic.gapt.expr.hol.{structuralCNF, univclosure}
import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.expansionTrees.{minimalExpansionSequent, ExpansionProofToLK}
import at.logic.gapt.proofs.resolution.expansionProofFromInstances
import at.logic.gapt.proofs.{FOLClause, Sequent}
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

// val stdinLines = Stream.continually(Console.in.readLine()).takeWhile(_ != null)

val endSequent =
  """
    p(0,y)
    p(x,f(y)) -> p(s(x),y)
    p(x,c) -> q(x,g(x))
    q(x,y) -> r(x)
    -r(s(s(s(s(0)))))
  """.split("\n").
  map(_.trim).
  filter(_.nonEmpty).
  map(parseFormula).
  map(univclosure(_)) ++: Sequent()

val (cnf, justifications, definitions) = structuralCNF(endSequent, generateJustifications = true, propositional = false)

val done = mutable.Set[FOLClause]()
val todo = mutable.Queue[FOLClause](cnf.toSeq: _*)
while (Sat4j solve (done ++ todo) isDefined) {
  val next = todo.dequeue()
  if (!done.contains(next)) for {
    clause2 <- done
    clause1 = FOLSubstitution(rename(freeVariables(next), freeVariables(clause2)))(next)
    (atom1,index1) <- clause1.zipWithIndex.elements
    (atom2,index2) <- clause2.zipWithIndex.elements
    if !index2.sameSideAs(index1)
    mgu <- syntacticMGU(atom1, atom2)
  } todo ++= Seq(mgu(clause1), mgu(clause2))
  done += next
}

val instances =
  for (clause <- cnf) yield
    clause -> (for {
      inst <- done ++ todo
      subst <- syntacticMatching(clause.toFormula, inst.toFormula)
    } yield subst).toSet

val expansionProof = expansionProofFromInstances(instances.toMap, endSequent, justifications, definitions)
val Some(minimizedExpansionProof) = minimalExpansionSequent(expansionProof, Sat4j)

val lkProof = ExpansionProofToLK(minimizedExpansionProof)
println(lkProof)
prooftool(lkProof)

