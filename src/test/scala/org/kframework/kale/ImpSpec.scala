package org.kframework.kale

import org.scalatest.FreeSpec

/*
module IMP-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => M[X] ...</k> <state> M:Map </state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state> M:Map => M[X <- I] </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map => Rho[X <- 0] </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule
 */

object IMP {
  implicit val env = new Environment

  import env._
  import builtin._

  // signature

  val AExpInt = FreeLabel1("_:Int->AExp")
  val AExpId = FreeLabel1("_:Id->AExp")
  val AExpDiv = FreeLabel2("_/_:AExp*AExp->AExp")
  val AExpPlus = FreeLabel2("_+_:AExp*AExp->AExp")

  val BExpBool = FreeLabel1("_:Bool->BExp")
  val BExpLeq = FreeLabel2("_<=_:AExp*AExp->BExp")
  val BExpNot = FreeLabel2("!_:BExp->BExp")
  val BExpAnd = FreeLabel2("_&&_:BExp*BExp->BExp")

  val BlockEmpty = FreeLabel0("{}:->Block")
  val BlockStmt = FreeLabel1("{_}:Stmt->Block")

  val StmtBlock = FreeLabel1("_:Block->Stmt")
  val StmtAssign = FreeLabel2("_=_;:Id*AExp->Stmt")
  val StmtIf = FreeLabel3("if(_)_else_:BExp*Block*Block->Stmt")
  val StmtWhile = FreeLabel2("while(_)_:BExp*Block->Stmt")
  val StmtSeq = FreeLabel2("__:Stmt*Stmt->Stmt")

  val Pgm = FreeLabel2("int_;_:List{Id}*Stmt->Pgm")

  val IdsCons = FreeLabel2("_,_:Id*List{Id}->List{Id}")
  val IdsNil = FreeLabel0(".List:->List{Id}")

  val KAExp = FreeLabel1("_:AExp->K")
  val KBExp = FreeLabel1("_:BExp->K")
  val KBlock = FreeLabel1("_:Block->K")
  val KStmt = FreeLabel1("_:Stmt->K")
  val KPgm = FreeLabel1("_:Pgm->K")

  // configuration

  val T = FreeLabel2("<T>:Cell*Cell->Cell")
  val k = FreeLabel1("<k>:List{K}->Cell")
  val state = FreeLabel1("<state>:Map{Id,Int}->Cell")

  val kCons = FreeLabel2("_~>_:K*List{K}->List{K}")
  val kNil = FreeLabel0(".K:->List{K}")

  val MapIdIntInsert = FreeLabel3("_[_<-_]:Map{Id,Int}*Id*Int->Map{Id,Int}")
  val MapIdIntLookup = FreeLabel2("_[_]:Map{Id,Int}*Id->Int")
  val MapIdEmpty = FreeLabel0(".Map:->Map{Id,Int}")

  // rules

//  val varBinding = FreeLabel2("_->_")
//
//  val emptyStates = FreeLabel0("emptyStates")
//  val statesMap = MapLabel("_StatesMap_", {
//    case varBinding(variable, _) => variable
//  }, emptyStates())


  val intDiv = PrimitiveFunction2("_/Int_", INT, (a: Int, b: Int) => a / b)

//  case class isSort(label: LeafLabel[_])(implicit val env: Environment) extends {
//    val name: String = "is" + label.name
//  } with PurelyFunctionalLabel1 {
//    def f(_1: Term): Option[Term] = Some(Truth(_1.label == label))
//  }
//
//  val isInt = isSort(INT)

  val X = Variable("X:Id")
  val M = Variable("M:Map{Id,Int}")
  val I = Variable("I:Int")
  val I1 = Variable("I1:Int")
  val I2 = Variable("I2:Int")
  val B = Variable("B:Bool")
  val S = Variable("S:Stmt")
  val S1 = Variable("S1:Stmt")
  val S2 = Variable("S2:Stmt")
  val Ks = Variable("Ks:List{K}")

  def lhs(t: Term): Term = t match {
    case Rewrite(l, r) => l
    case Node(label, children) => label(children.toSeq map lhs)
    case o => o
  }

  def rhs(t: Term): Term = t match {
    case Rewrite(l, r) => r
    case Node(label, children) => label(children.toSeq map rhs)
    case o => o
  }

  val implicits = new Implicits()
  import implicits._

  val rules = Set(
    T(k(kCons(KAExp(Rewrite(AExpId(X), AExpInt(MapIdIntLookup(M,X)))), Ks)), state(M))
  , T(k(kCons(KAExp(Rewrite(AExpDiv(AExpInt(I1), AExpInt(I2)), AExpInt(intDiv(I1, I2)))), Ks)), state(M))
  ) map (t => Rewrite(lhs(t), rhs(t)))

  ID("junk")

  env.seal()

  val matcher = Matcher(env).default
  val substitutionApplier = SubstitutionApply(env)
  val rewrite = Rewriter(substitutionApplier, matcher, env)(rules)
}

class ImpSpec extends FreeSpec {
  "IMP" - {

    import IMP._
    import IMP.env._
    import IMP.env.builtin._
    import implicits._

    val term = T(k(kCons(KAExp(AExpId(ID("foo"))), kNil())), state(MapIdIntInsert(MapIdEmpty(),ID("foo"),5)))

    println(rewrite.searchStep(term))

    //    println(TCell(kCell(KSEQ.unit), stateCell(emptyState)))
  }
}


//object IMP {
//  class Production0(val name: String) extends Label0 with InModule
//  class Production1(val name: String) extends Label1 with InModule
//  class Production2(val name: String) extends Label2 with InModule with SimpleNode2Label
//  class Production3(val name: String) extends Label3 with InModule
//
//  object + extends Production2("+")
//  object - extends Production2("-")
//  object <= extends Production1("<=")
//  object ! extends Production1("!")
//  object && extends Production2("&&")
//
//  object Block extends Production1("{_}")
//  object Assign extends Production1("_=_;")
//  object IfThenElse extends Production3("if_then_else_")
//  object Pgm extends Production2("int _ ; _")
//
//
//  val IdsModule = new ASSOC_LIST("_,_", new Production0(".Ids").apply())
//  val ids = IdsModule.opLabel
//  val emptyIds = IdsModule.unit
//
//  val StmtsModule = new ASSOC_LIST("_;_", new Production0(".Stmts").apply())
//  val stmts = StmtsModule.op
//  val emptyStmts = StmtsModule.unit
//
//  object TCell extends Production2("<T>")
//  object kCell extends Production1("<k>")
//  object stateCell extends Production1("<state>")
//  val StateModule = new MAP(" ", "|->", new Production0(".State").apply())
//  val state = StateModule.op
//  val emptyState = StateModule.unit
//  override def unify(a: Term, b: Term): Term = ???
//}
