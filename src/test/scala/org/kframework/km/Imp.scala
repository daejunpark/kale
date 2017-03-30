package org.kframework.km

object Imp {

  import term._
  import builtin._

  class Constructor1(override val name: String, override val signature: Type) extends Constructor(name, signature) {
    override def toString: String = if (name.contains(':')) name.substring(0, name.indexOf(':')) else name
  }

  // signature

  val Id = SortOf("Id")
  val ListId = SortList(Id)

  val AExp = SortOf("AExp")
  val BExp = SortOf("BExp")
  val Exp = SortOf("Exp")
  val Block = SortOf("Block")
  val Stmt = SortOf("Stmt")
  val Pgm = SortOf("Pgm")

  val IdOf = new Constructor1("_:String->Id", (Seq(SortString), Id))

  val AExpInt = new Constructor1("_:Int->AExp", (Seq(SortInt), AExp))
  val AExpId = new Constructor1("_:Id->AExp", (Seq(Id), AExp))
  val AExpDiv = new Constructor1("_/_:AExp*AExp->AExp", (Seq(AExp, AExp), AExp))
  val AExpPlus = new Constructor1("_+_:AExp*AExp->AExp", (Seq(AExp, AExp), AExp))

  val BExpBool = new Constructor1("_:Bool->BExp", (Seq(SortBool), BExp))
  val BExpLeq = new Constructor1("_<=_:AExp*AExp->BExp", (Seq(AExp, AExp), BExp))
  val BExpNot = new Constructor1("!_:BExp->BExp", (Seq(BExp), BExp))
  val BExpAnd = new Constructor1("_&&_:BExp*BExp->BExp", (Seq(BExp, BExp), BExp))

  val BlockEmpty = new Constructor1("{}:->Block", (Seq(), Block))
  val BlockStmt = new Constructor1("{_}:Stmt->Block", (Seq(Stmt), Block))

  val StmtBlock = new Constructor1("_:Block->Stmt", (Seq(Block), Stmt))
  val StmtAssign = new Constructor1("_=_;:Id*AExp->Stmt", (Seq(Id, AExp), Stmt))
  val StmtIf = new Constructor1("if(_)_else_:BExp*Block*Block->Stmt", (Seq(BExp, Block, Block), Stmt))
  val StmtWhile = new Constructor1("while(_)_:BExp*Block->Stmt", (Seq(BExp, Block), Stmt))
  val StmtSeq = new Constructor1("__:Stmt*Stmt->Stmt", (Seq(Stmt, Stmt), Stmt))

  val PgmOf = new Constructor1("int_;_:List{Id}*Stmt->Pgm", (Seq(ListId, Stmt), Pgm))

  val IdsCons = new Constructor1("_,_:Id*List{Id}->List{Id}", (Seq(Id, ListId), ListId))
  val IdsNil = new Constructor1(".List:->List{Id}", (Seq(), ListId))

  val KAExp = new Constructor1("_:AExp->K", (Seq(AExp), SortK))
  val KBExp = new Constructor1("_:BExp->K", (Seq(BExp), SortK))
  val KBlock = new Constructor1("_:Block->K", (Seq(Block), SortK))
  val KStmt = new Constructor1("_:Stmt->K", (Seq(Stmt), SortK))
  val KPgm = new Constructor1("_:Pgm->K", (Seq(Pgm), SortK))

  // configuration

  val Cell = SortOf("Cell")

  val T = new Constructor1("<T>:Cell*Cell->Cell", (Seq(Cell, Cell), Cell))
  val k = new Constructor1("<k>:List{K}->Cell", (Seq(SortListK), Cell))
  val state = new Constructor1("<state>:Map{Id,Int}->Cell", (Seq(SortMapK), Cell))

  val kCons = new Constructor1("_~>_:K*List{K}->List{K}", (Seq(SortK, SortListK), SortListK))
  val kNil = new Constructor1(".K:->List{K}", (Seq(), SortListK))

  // rules

  val X = Variable("X", Id)
  val Xs = Variable("Xs", ListId)
  val M = Variable("M", SortMapK)
  val I = Variable("I", SortInt)
  val I1 = Variable("I1", SortInt)
  val I2 = Variable("I2", SortInt)
  val B = Variable("B", SortBool)
  val S = Variable("S", Stmt)
  val S1 = Variable("S1", Stmt)
  val S2 = Variable("S2", Stmt)
  val Ks = Variable("Ks", SortListK)
  val Be = Variable("Be", BExp)
  val Be1 = Variable("Be1", BExp)
  val Be2 = Variable("Be2", BExp)
  val Blk = Variable("Blk", Block)
  val Blk1 = Variable("Blk1", Block)
  val Blk2 = Variable("Blk2", Block)
  val E1 = Variable("E1", AExp)
  val E2 = Variable("E2", AExp)

  val tt = BOOL(true)

  val freezerDiv0 = new Constructor1("freezer_/_0:AExp->K", (Seq(AExp), SortK))
  val freezerDiv1 = new Constructor1("freezer_/_1:AExp->K", (Seq(AExp), SortK))
  val freezerPlus0 = new Constructor1("freezer_+_0:AExp->K", (Seq(AExp), SortK))
  val freezerPlus1 = new Constructor1("freezer_+_1:AExp->K", (Seq(AExp), SortK))
  val freezerLeq0 = new Constructor1("freezer_<=_0:AExp->K", (Seq(AExp), SortK))
  val freezerLeq1 = new Constructor1("freezer_<=_1:AExp->K", (Seq(AExp), SortK))
  val freezerNot0 = new Constructor1("freezer!_0:->K", (Seq(), SortK))
  val freezerAnd0 = new Constructor1("freezer_&&_0:BExp->K", (Seq(BExp), SortK))
  val freezerAssign1 = new Constructor1("freezer_=_;1:Id->K", (Seq(Id), SortK))
  val freezerIf0 = new Constructor1("freezerif(_)_else_0:Block*Block->K", (Seq(Block, Block), SortK))


  object isKResult extends Symbol {
    override val name: String = "isKResult"
    override val smt: String = "isKResult"
    override val smtBuiltin: Boolean = false
    override val signature: Type = (Seq(SortK), SortBool)
    override val isFunctional: Boolean = true
    override def applySeq(children: Seq[Term]): Term = {
      assert(children.size == 1)
      val default = Application(this, children)
      val t = children(0)
      t match {
        case Application(`KAExp`, Seq(Application(`AExpInt`, Seq(_)))) => BOOL(true)
        case Application(`KAExp`, Seq(Variable(_,_))) => default
        case Application(`KBExp`, Seq(Application(`BExpBool`, Seq(_)))) => BOOL(true)
        case Application(`KBExp`, Seq(Variable(_,_))) => default
        case Variable(_,_) => default
        case _ => BOOL(false)
      }
    }
  }

  implicit class infixTerm(p: Term) {
    def ~>:(q: Term): Term = kCons(q, p)
    def /\(q: Term): Term = BOOL.and(p, q)
  }

  val rules = Seq(
    // AExp
      SimpleRewrite(
      T(k(KAExp(AExpId(X)) ~>: Ks), state(M)),
      T(k(MAP_K.select(M, KAExp(AExpId(X))) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KAExp(AExpDiv(AExpInt(I1), AExpInt(I2))) ~>: Ks), state(M)),
      T(k(KAExp(AExpInt(INT.div(I1, I2))) ~>: Ks), state(M)),
      BOOL.not(EQ.of(SortInt)(I1, INT(0))))
    , SimpleRewrite(
      T(k(KAExp(AExpPlus(AExpInt(I1), AExpInt(I2))) ~>: Ks), state(M)),
      T(k(KAExp(AExpInt(INT.plus(I1, I2))) ~>: Ks), state(M)),
      tt)
    // BExp
    , SimpleRewrite(
      T(k(KBExp(BExpLeq(AExpInt(I1), AExpInt(I2))) ~>: Ks), state(M)),
      T(k(KBExp(BExpBool(INT.le(I1, I2))) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KBExp(BExpNot(BExpBool(B))) ~>: Ks), state(M)),
      T(k(KBExp(BExpBool(BOOL.not(B))) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KBExp(BExpAnd(BExpBool(BOOL(true)), Be)) ~>: Ks), state(M)),
      T(k(KBExp(Be) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KBExp(BExpAnd(BExpBool(BOOL(false)), Be)) ~>: Ks), state(M)),
      T(k(KBExp(BExpBool(BOOL(false))) ~>: Ks), state(M)),
      tt)
    // Block
    , SimpleRewrite(
      T(k(KStmt(StmtBlock(BlockEmpty())) ~>: Ks), state(M)),
      T(k(Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KStmt(StmtBlock(BlockStmt(S))) ~>: Ks), state(M)),
      T(k(KStmt(S) ~>: Ks), state(M)),
      tt)
    // Stmt
    , SimpleRewrite(
      T(k(KStmt(StmtAssign(X, AExpInt(I))) ~>: Ks), state(M)),
      T(k(Ks), state(MAP_K.store(M, KAExp(AExpId(X)), KAExp(AExpInt(I))))),
      tt)
    , SimpleRewrite(
      T(k(KStmt(StmtSeq(S1,S2)) ~>: Ks), state(M)),
      T(k(KStmt(S1) ~>: KStmt(S2) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KStmt(StmtIf(BExpBool(BOOL(true)), Blk1, Blk2)) ~>: Ks), state(M)),
      T(k(KStmt(StmtBlock(Blk1)) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KStmt(StmtIf(BExpBool(BOOL(false)), Blk1, Blk2)) ~>: Ks), state(M)),
      T(k(KStmt(StmtBlock(Blk2)) ~>: Ks), state(M)),
      tt)
    , SimpleRewrite(
      T(k(KStmt(StmtWhile(Be, Blk)) ~>: Ks), state(M)),
      T(k(KStmt(StmtIf(Be, BlockStmt(StmtSeq(StmtBlock(Blk), StmtWhile(Be, Blk))), BlockEmpty())) ~>: Ks), state(M)),
      tt)
    // Pgm
    , SimpleRewrite(
      T(k(KPgm(PgmOf(IdsCons(X, Xs), S)) ~>: Ks), state(M)),
      T(k(KPgm(PgmOf(Xs, S)) ~>: Ks), state(MAP_K.store(M, KAExp(AExpId(X)), KAExp(AExpInt(INT(0)))))),
      tt)
    , SimpleRewrite(
      T(k(KPgm(PgmOf(IdsNil(), S)) ~>: Ks), state(M)),
      T(k(KStmt(S) ~>: Ks), state(M)),
      tt)
    // strict
    // AExpDiv
    , SimpleRewrite(
      T(k(KAExp(AExpDiv(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E1) ~>: freezerDiv0(E2) ~>: Ks), state(M)),
      BOOL.not(isKResult(KAExp(E1))))
    , SimpleRewrite(
      T(k(KAExp(E1) ~>: freezerDiv0(E2) ~>: Ks), state(M)),
      T(k(KAExp(AExpDiv(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E1)))
    , SimpleRewrite(
      T(k(KAExp(AExpDiv(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E2) ~>: freezerDiv1(E1) ~>: Ks), state(M)),
      BOOL.and(isKResult(KAExp(E1)), BOOL.not(isKResult(KAExp(E2)))))
    , SimpleRewrite(
      T(k(KAExp(E2) ~>: freezerDiv1(E1) ~>: Ks), state(M)),
      T(k(KAExp(AExpDiv(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E2)))
    // AExpPlus
    , SimpleRewrite(
      T(k(KAExp(AExpPlus(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E1) ~>: freezerPlus0(E2) ~>: Ks), state(M)),
      BOOL.not(isKResult(KAExp(E1))))
    , SimpleRewrite(
      T(k(KAExp(E1) ~>: freezerPlus0(E2) ~>: Ks), state(M)),
      T(k(KAExp(AExpPlus(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E1)))
    , SimpleRewrite(
      T(k(KAExp(AExpPlus(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E2) ~>: freezerPlus1(E1) ~>: Ks), state(M)),
      BOOL.and(isKResult(KAExp(E1)), BOOL.not(isKResult(KAExp(E2)))))
    , SimpleRewrite(
      T(k(KAExp(E2) ~>: freezerPlus1(E1) ~>: Ks), state(M)),
      T(k(KAExp(AExpPlus(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E2)))
    // BExpLeq
    , SimpleRewrite(
      T(k(KBExp(BExpLeq(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E1) ~>: freezerLeq0(E2) ~>: Ks), state(M)),
      BOOL.not(isKResult(KAExp(E1))))
    , SimpleRewrite(
      T(k(KAExp(E1) ~>: freezerLeq0(E2) ~>: Ks), state(M)),
      T(k(KBExp(BExpLeq(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E1)))
    , SimpleRewrite(
      T(k(KBExp(BExpLeq(E1, E2)) ~>: Ks), state(M)),
      T(k(KAExp(E2) ~>: freezerLeq1(E1) ~>: Ks), state(M)),
      BOOL.and(isKResult(KAExp(E1)), BOOL.not(isKResult(KAExp(E2)))))
    , SimpleRewrite(
      T(k(KAExp(E2) ~>: freezerLeq1(E1) ~>: Ks), state(M)),
      T(k(KBExp(BExpLeq(E1, E2)) ~>: Ks), state(M)),
      isKResult(KAExp(E2)))
    // BExpNot
    , SimpleRewrite(
      T(k(KBExp(BExpNot(Be)) ~>: Ks), state(M)),
      T(k(KBExp(Be) ~>: freezerNot0() ~>: Ks), state(M)),
      BOOL.not(isKResult(KBExp(Be))))
    , SimpleRewrite(
      T(k(KBExp(Be) ~>: freezerNot0() ~>: Ks), state(M)),
      T(k(KBExp(BExpNot(Be)) ~>: Ks), state(M)),
      isKResult(KBExp(Be)))
    // BExpAnd
    , SimpleRewrite(
      T(k(KBExp(BExpAnd(Be1, Be2)) ~>: Ks), state(M)),
      T(k(KBExp(Be1) ~>: freezerAnd0(Be2) ~>: Ks), state(M)),
      BOOL.not(isKResult(KBExp(Be1))))
    , SimpleRewrite(
      T(k(KBExp(Be1) ~>: freezerAnd0(Be2) ~>: Ks), state(M)),
      T(k(KBExp(BExpAnd(Be1, Be2)) ~>: Ks), state(M)),
      isKResult(KBExp(Be1)))
    // StmtAssign
    , SimpleRewrite(
      T(k(KStmt(StmtAssign(X, E1)) ~>: Ks), state(M)),
      T(k(KAExp(E1) ~>: freezerAssign1(X) ~>: Ks), state(M)),
      BOOL.not(isKResult(KAExp(E1))))
    , SimpleRewrite(
      T(k(KAExp(E1) ~>: freezerAssign1(X) ~>: Ks), state(M)),
      T(k(KStmt(StmtAssign(X, E1)) ~>: Ks), state(M)),
      isKResult(KAExp(E1)))
    // StmtIf
    , SimpleRewrite(
      T(k(KStmt(StmtIf(Be, Blk1, Blk2)) ~>: Ks), state(M)),
      T(k(KBExp(Be) ~>: freezerIf0(Blk1, Blk2) ~>: Ks), state(M)),
      BOOL.not(isKResult(KBExp(Be))))
    , SimpleRewrite(
      T(k(KBExp(Be) ~>: freezerIf0(Blk1, Blk2) ~>: Ks), state(M)),
      T(k(KStmt(StmtIf(Be, Blk1, Blk2)) ~>: Ks), state(M)),
      isKResult(KBExp(Be)))
  )

}
