using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny;
using EnvDTE;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.ComponentModelHost;
using Microsoft.VisualStudio.Editor;
using Microsoft.Boogie;
using System.IO;
using Microsoft.VisualStudio.Text;
using static Microsoft.Dafny.CalcStmt;
using Microsoft.VisualStudio.Shell.Interop;
//calcstmt
//selectedstmts -- bids func doesnt work for stmts inside other stmts
//selectedstmts from laddon -- make sure it supports all stmts and expressions etc..
//extract lemma
namespace Extract_Inline_Method
{
    class HelpFunctions
    {
        public static Statement SelectionScope;


        public static int getNextIndex(string name,List<DVariable> ins,List<DVariable> outs,List<DVariable> toDecl)
        {
            int max = -1;
            foreach (var x in ins)
            {
                if (x.name.Length >= name.Length)
                {
                    if (strncmp(x.name,name,name.Length))
                    {
                        var temp = getNum(x.name);
                        if (temp > max) max = temp;
                    }
                }
            }
            foreach (var x in outs)
            {
                if (x.name.Length >= name.Length)
                {
                    if (strncmp(x.name, name, name.Length))
                    {
                        var temp = getNum(x.name);
                        if (temp > max) max = temp;
                    }
                }
            }
            foreach (var x in toDecl)
            {
                if (x.name.Length >= name.Length)
                {
                    if (strncmp(x.name, name, name.Length))
                    {
                        var temp = getNum(x.name);
                        if (temp > max) max = temp;
                    }
                }
            }
            return max+1;
        }
        public static int getNum(string name)
        {
            if (name.Length < 1) return -1;
            if (name[name.Length - 1] < '0' || name[name.Length - 1] > '9') return -1;
            int index = -1;
            for(int i = name.Length - 1; i >= 0; i--)
            {
                if (name[i] < '0' || name[i] > '9')
                {
                    index = i + 1;
                    break;
                }
            }
            return Int32.Parse(name.Substring(index));
        }

        public static Boolean strncmp(string first,string second,int len)
        {
            if (first.Length < len || second.Length < len) return false;
            for(int i = 0; i < len; i++)
            {
                if (first[i] != second[i]) return false;
            }
            return true;
        }
        //laddon
        public static List<Statement> GetSelectedStatements(out List<Statement> otherStatements)
        {
            var method = GetCurrentMethod();
            var textView = GetWpfView();
            var start = textView.Selection.Start.Position;
            var end = textView.Selection.End.Position;
            List<Statement> statements = new List<Statement>();
            otherStatements = new List<Statement>();
            foreach (var statement in method.Body.Body)
            {
                if (statement.Tok.pos >= start && statement.Tok.pos <= end)
                    statements.Add(statement);
                else if (statement.Tok.pos > end)
                    otherStatements.Add(statement);

            }
            return statements;
        }

        //not used
        public static void prettyPrint(string fileName)
        {
            DTE dte = (DTE)ExtractMethodPackage.GetGlobalService(typeof(DTE));
            TextWriter x = new StringWriter();
            Printer p = new Printer(x);
            dte.ActiveDocument.Save();
            p.PrintProgram(HelpFunctions.GetProgram(fileName), false);
            var resultText = x.ToString();

            //get length of doc
            TextDocument doc = (TextDocument)(dte.ActiveDocument.Object("TextDocument"));
            var pp = doc.StartPoint.CreateEditPoint();
            string s = pp.GetText(doc.EndPoint);

            ITextEdit edit = HelpFunctions.GetWpfView().TextBuffer.CreateEdit();
            edit.Delete(0,s.Length);
            edit.Insert(0, resultText);
            edit.Apply();
            dte.ActiveDocument.Save();
        }

        //biadsy
        public static void GetVariables(List<Statement> statements, List<Statement> otherStatements, out List<DVariable> ins, out List<DVariable> outs, out List<DVariable> toDeclare)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> varsDeclaredInSelectedScope;
            var varsUsedInSelectedScope = GetVars(statements, out varsDeclaredInSelectedScope, true);
            HashSet<DVariable> t;
            var varsModifiedInSelectedScope = GetVars(statements, out t, false).ToList();
            HashSet<DVariable> varsDeclaredAfterScope;
            var varsUsedAfterScope = GetVars(otherStatements, out varsDeclaredAfterScope, true);
            ins = varsUsedInSelectedScope.ToList();
            //          outs = varsModifiedInSelectedScope.Intersect(varsUsedAfterScope, comparer).ToList();
            outs = varsModifiedInSelectedScope;
            toDeclare = varsDeclaredInSelectedScope.Intersect(varsUsedAfterScope, comparer).ToList();

        }
        //biadsy
        public static HashSet<DVariable> GetVars(List<Statement> statements, out HashSet<DVariable> declVars, bool containNonModified)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> vars = new HashSet<DVariable>(comparer);
            declVars = new HashSet<DVariable>(comparer);
            foreach (var stmt in statements)
            {
                vars.UnionWith(GetVars(stmt, declVars, containNonModified));
            }

            return vars;

        }
        //biadsy
        private static HashSet<DVariable> GetVars(Statement stmt, HashSet<DVariable> declaredVars, bool containNonModified)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> usedVars = new HashSet<DVariable>(comparer);
            if (stmt is UpdateStmt)
            {
                var ustmt = (UpdateStmt)stmt;
                foreach (var ls in ustmt.Lhss)
                {
                    usedVars.UnionWith(GetVars(ls, declaredVars));
                }
                if (containNonModified)
                {
                    foreach (var rs in ustmt.Rhss)
                    {
                        var exp = rs as ExprRhs;
                        usedVars.UnionWith(GetVars(exp.Expr, declaredVars));
                    }
                }
            }
            else if (stmt is AssertStmt && containNonModified)
            {
                var asrt = stmt as AssertStmt;
                usedVars.UnionWith(GetVars(asrt.Expr, declaredVars));
                usedVars.UnionWith(GetVars(asrt.Proof, declaredVars, containNonModified));

            }
            else if (stmt is WhileStmt)
            {
                var wstmt = stmt as WhileStmt;
                usedVars.UnionWith(GetVars(wstmt.Body, declaredVars, containNonModified));
                foreach (var exp in wstmt.Decreases.Expressions)
                    usedVars.UnionWith(GetVars(exp, declaredVars));
                usedVars.UnionWith(GetVars(wstmt.Guard, declaredVars));
                foreach (var exp in wstmt.Invariants)
                    usedVars.UnionWith(GetVars(exp.E, declaredVars));
            }
            else if (stmt is BlockStmt)
            {
                var stmts = stmt as BlockStmt;
                foreach (var bodyStmt in stmts.Body)
                {
                    usedVars.UnionWith(GetVars(bodyStmt, declaredVars, containNonModified));
                }

            }
            else if(stmt is CalcStmt)
            {
                var calcstmt = stmt as CalcStmt;
                foreach(var x in calcstmt.Lines)
                {
                    usedVars.UnionWith(GetVars(x,declaredVars));
                }
                foreach (var x in calcstmt.Hints)
                {
                    usedVars.UnionWith(GetVars(x, declaredVars, containNonModified));
                }
                foreach (var x in calcstmt.Steps)
                {
                    usedVars.UnionWith(GetVars(x, declaredVars));
                }
            }
            else if (stmt is VarDeclStmt)
            {
                var decl = stmt as VarDeclStmt;
                usedVars.UnionWith(GetVars(decl.Update, declaredVars, containNonModified));
                if (decl.Locals != null)
                {
                    foreach (var v in decl.Locals)
                    {
                        DVariable dvar = new DVariable(v.DisplayName, v.Type);
                        declaredVars.Add(dvar);
                    }
                }

            }
            else if (stmt is IfStmt)
            {
                var ifstmt = stmt as IfStmt;
                usedVars.UnionWith(GetVars(ifstmt.Guard, declaredVars));
                usedVars.UnionWith(GetVars(ifstmt.Thn, declaredVars, containNonModified));
                usedVars.UnionWith(GetVars(ifstmt.Els, declaredVars, containNonModified));
            }
            else if (stmt is PrintStmt)
            {
                var pstmt = stmt as PrintStmt;
                foreach (var arg in pstmt.Args)
                    usedVars.UnionWith(GetVars(arg, declaredVars));
            }

            return usedVars;
        }
        //biadsy
        private static HashSet<DVariable> GetVars(Microsoft.Dafny.Expression exp, HashSet<DVariable> declaredVars)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> vars = new HashSet<DVariable>(comparer);
            if (exp is SeqSelectExpr)
            {
                var expr = exp as SeqSelectExpr;
                vars.UnionWith(GetVars(expr.Seq, declaredVars));
                vars.UnionWith(GetVars(expr.E0, declaredVars));
                vars.UnionWith(GetVars(expr.E1, declaredVars));
            }
            else if (exp is NameSegment)
            {
                var expr = exp as NameSegment;
                DVariable var = new DVariable(expr.Name, expr.Type);
                if (!declaredVars.Contains(var))
                {

                    vars.Add(var);
                }

            }
            else if (exp is ApplySuffix)
            {
                var expr = exp as ApplySuffix;
                foreach (var arg in expr.Args)
                    vars.UnionWith(GetVars(arg, declaredVars));
            }
            else if (exp is BinaryExpr)
            {
                var expr = exp as BinaryExpr;
                vars.UnionWith(GetVars(expr.E0, declaredVars));
                vars.UnionWith(GetVars(expr.E1, declaredVars));
            }
            else if (exp is UnaryOpExpr)
            {
                var expr = exp as UnaryOpExpr;
                vars.UnionWith(GetVars(expr.E, declaredVars));
            }
            else if (exp is ParensExpression)
            {
                var expr = exp as ParensExpression;
                vars.UnionWith(GetVars(expr.E, declaredVars));
            }
            else if (exp is ChainingExpression)
            {
                var expr = exp as ChainingExpression;
                vars.UnionWith(GetVars(expr.E, declaredVars));
            }
            else if (exp is SeqDisplayExpr)
            {
                var expr = exp as SeqDisplayExpr;
                foreach (var arg in expr.Elements)
                    vars.UnionWith(GetVars(arg, declaredVars));
            }
            else if (exp is Microsoft.Dafny.ForallExpr)
            {
                var expr = exp as Microsoft.Dafny.ForallExpr;
                var newDecVars = new HashSet<DVariable>(declaredVars, comparer);
                if (expr.BoundVars != null)
                {
                    foreach (var bvar in expr.BoundVars)
                    {
                        DVariable dvar = new DVariable(bvar.DisplayName, bvar.Type);
                        newDecVars.Add(dvar);
                    }
                }
                vars.UnionWith(GetVars(expr.Term, newDecVars));
            }
            return vars;
        }

        //laddon
        public static Method FindMethod(string filename, int offset)
        {
            // This was commented since it was causing verification to crash. (Boogie is likely to be the source)
            // DafnyOptions.Install(new DafnyOptions());
            var program = GetProgram(filename);
            var decls = program.Modules().SelectMany(m => m.TopLevelDecls).ToList();
            var callables = ModuleDefinition.AllCallables(decls);

            var method = callables.Where(c => c is Method
                && ((Method)c).tok.pos <= offset
                && ((Method)c).BodyEndTok.pos >= offset);

            if (method.Any())
            {
                return method.First() as Method;
            }
            else
            {
                return null;
            }
        }
        public static Statement renameB(Statement stmt, Dictionary<string,string> rename)
        {
            if (stmt == null) return null;
            if (stmt is AssignStmt)
            {
                var x = stmt as AssignStmt;
                return new AssignStmt(null, null, renameB(x.Lhs,rename),renameB(x.Rhs,rename));
            }
            else if (stmt is UpdateStmt)
            {
                var x = stmt as UpdateStmt;
                List<AssignmentRhs> R = new List<AssignmentRhs>();
                foreach (var st in ((UpdateStmt)stmt).Rhss)
                {
                    R.Add(renameB(st, rename));
                }
                List<Microsoft.Dafny.Expression> L = new List<Microsoft.Dafny.Expression>();
                foreach (var st in ((UpdateStmt)stmt).Lhss)
                {
                    L.Add(renameB(st,rename));
                }
                return new UpdateStmt(null, null, L,R);
                //((UpdateStmt)statement).Lhss.ForEach(x => renameBody(x, rename));
            }
            else if (stmt is WhileStmt)
            {
                var x = stmt as WhileStmt;
                List<MaybeFreeExpression> R = new List<MaybeFreeExpression>();
                foreach (var st in x.Invariants)
                {
                    R.Add(renameB(st,rename));
                }
                return new WhileStmt(null, null, renameB(x.Guard,rename),R,renameB(x.Decreases,rename),renameB(x.Mod,rename),(BlockStmt)renameB(x.Body,rename));
            }
            else if (stmt is IfStmt)
            {
                var x = stmt as IfStmt;
                return new IfStmt(null, null, x.IsExistentialGuard,renameB(x.Guard,rename),(BlockStmt)renameB(x.Thn,rename),renameB(x.Els,rename));
            }
            else if (stmt is BlockStmt)
            {
                var x = stmt as BlockStmt;
                List<Statement> R = new List<Statement>();
                foreach (var st in x.SubStatements)
                {
                    R.Add(renameB(st, rename));
                }
                return new BlockStmt(null, null, R);
            }
            else if (stmt is AssertStmt)
            {
                var x = stmt as AssertStmt;
                return new AssertStmt(null, null, renameB(x.Expr,rename),(BlockStmt)renameB(x.Proof,rename),x.Attributes);
            }
            else if (stmt is VarDeclStmt)
            {
                var x = stmt as VarDeclStmt;
                List<LocalVariable> R = new List<LocalVariable>();
                for (int i = 0; i < x.Locals.Count; i++)
                {
                    var temp = x.Locals[i];
                    R.Add(renameB(temp,rename));
                }
                return new VarDeclStmt(null, null, R,(ConcreteUpdateStatement)renameB(x.Update,rename));
            }
            //else if (stmt is ConcreteUpdateStatement)
            //{
            //    var x = stmt as ConcreteUpdateStatement;
            //    List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
            //    foreach (var st in x.Lhss)
            //    {
            //        R.Add(renameB(st, rename));
            //    }
            //    return new ConcreteUpdateStatement(x.Tok,x.EndTok,R,x.Attributes);
            //}
            else if (stmt is CallStmt)
            {
                var x = stmt as CallStmt;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                List<Microsoft.Dafny.Expression> L = new List<Microsoft.Dafny.Expression>();
                foreach (var expr in x.Lhs)
                {
                    L.Add(renameB(expr, rename));
                }
                foreach (var expr in x.Args)
                {
                    R.Add(renameB(expr, rename));
                }
                return new CallStmt(null, null, L,(MemberSelectExpr)renameB(x.MethodSelect,rename),R);
            }
            else if (stmt is PrintStmt)
            {
                var x = stmt as PrintStmt;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                foreach (var expr in x.Args)
                {
                    R.Add(renameB(expr, rename));
                }
                return new PrintStmt(null, null, R);
            }
            else if (stmt is AssignSuchThatStmt)
            {
                var x = stmt as AssignSuchThatStmt;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                foreach (var expr in x.Lhss)
                {
                    R.Add(renameB(expr, rename));
                }
                return new AssignSuchThatStmt(null, null, R,renameB(x.Expr,rename),x.AssumeToken,x.Attributes);
            }
            else if (stmt is CalcStmt)
            {
                var x = stmt as CalcStmt;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                List<BlockStmt> L = new List<BlockStmt>();
                // throw new NotImplementedException(statement.ToString());
                foreach (var st in x.Hints)
                {
                    L.Add((BlockStmt)renameB(st, rename));
                }
                foreach (var st in x.Lines)
                {
                    R.Add(renameB(st,rename));
                }
                return new CalcStmt(null, null, x.UserSuppliedOp,R,L,x.StepOps,x.Attributes);
            }
            else
            {
                //throw new NotImplementedException("implement this!.");
                //return null;
                return stmt;
            }
        }
        
        public static Microsoft.Dafny.Expression renameB(Microsoft.Dafny.Expression expr,Dictionary<string,string> rename)
        {
            if (expr == null) return null;
            if (expr is ApplySuffix)
            {
                var x = expr as ApplySuffix;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                foreach (var exp in x.Args)
                {
                    R.Add(renameB(exp, rename));
                }

                //List<Microsoft.Dafny.Expression> x = new List<Microsoft.Dafny.Expression>(((ApplySuffix)expr).Args);
                //x.ForEach(m => renameBody(m, rename));
                //expr = new ApplySuffix(expr.tok, ((ApplySuffix)expr).Lhs, x);
                return new ApplySuffix(null, renameB(x.Lhs,rename),R);
            }
            else if (expr is NameSegment)
            {
                var x = expr as NameSegment;
                if (rename.ContainsKey(x.Name)) return new NameSegment(null, rename[x.Name], x.OptTypeArguments);
                else return expr;
            }
            else if (expr is BinaryExpr)
            {
                var x = expr as BinaryExpr;
                return new BinaryExpr(null, x.Op,renameB(x.E0,rename),renameB(x.E1,rename));
            }
            else if(expr is UnaryOpExpr)
            {
                var x = expr as UnaryOpExpr;
                return new UnaryOpExpr(null, x.Op,renameB(x.E,rename));
            }
            else if (expr is ConversionExpr)
            {
                var x = expr as ConversionExpr;
                return new ConversionExpr(null, renameB(x.E,rename),x.ToType);
            }
            else if (expr is ChainingExpression)
            {
                var x = expr as ChainingExpression;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                List<Microsoft.Dafny.Expression> L = new List<Microsoft.Dafny.Expression>();
                foreach (var exp in x.Operands)
                {
                    R.Add(renameB(exp, rename));
                }
                foreach (var exp in x.PrefixLimits)
                {
                    L.Add(renameB(exp,rename));
                }
                return new ChainingExpression(null, R,x.Operators,x.OperatorLocs,L);
            }
            else if (expr is SeqSelectExpr)
            {
                var x = expr as SeqSelectExpr;
                return new SeqSelectExpr(null, x.SelectOne,renameB(x.Seq,rename),renameB(x.E0,rename),renameB(x.E1,rename));
            }
            else if (expr is ParensExpression)
            {
                var x = expr as ParensExpression;
                return new ParensExpression(null, renameB(x.E,rename));
            }
            else if (expr is SeqDisplayExpr)
            {
                var x = expr as SeqDisplayExpr;
                List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
                foreach (var exp in x.Elements)
                {
                    R.Add(renameB(exp,rename));
                }
                return new SeqDisplayExpr(null, R);
            }
            else
            {
                //throw new NotImplementedException("implement this!.");
                //return null;
                return expr;
            }
        }

        public static LocalVariable renameB(LocalVariable v, Dictionary<string,string> rename)
        {
            if (rename.ContainsKey(v.Name)) return new LocalVariable(null, null, rename[v.Name], v.Type, v.IsGhost);
            else return v;
        }

        public static AssignmentRhs renameB(AssignmentRhs a, Dictionary<string, string> rename)
        {
            if (!(a is ExprRhs)) return null;
            return new ExprRhs(renameB(((ExprRhs)a).Expr,rename));
        }

        public static MaybeFreeExpression renameB(MaybeFreeExpression mbfe, Dictionary<string, string> rename)
        {
            return new MaybeFreeExpression(renameB(mbfe.E,rename));
        }

        public static FrameExpression renameB(FrameExpression v, Dictionary<string, string> rename)
        {
            return new FrameExpression(null, renameB(v.E,rename),v.FieldName);
        }

        public static Specification<Microsoft.Dafny.Expression> renameB(Specification<Microsoft.Dafny.Expression> spec, Dictionary<string,string> rename)
        {
            List<Microsoft.Dafny.Expression> R = new List<Microsoft.Dafny.Expression>();
            foreach (var sp in spec.Expressions)
            {
                R.Add(renameB(sp,rename));
            }
            return new Specification<Microsoft.Dafny.Expression>(R,spec.Attributes);
        }

        public static Specification<FrameExpression> renameB(Specification<FrameExpression> spec, Dictionary<string, string> rename)
        {
            List<FrameExpression> R = new List<FrameExpression>();
            foreach (var sp in spec.Expressions)
            {
                R.Add(renameB(sp, rename));
            }
            return new Specification<FrameExpression>(R, spec.Attributes);
        }


        public static void renameBody(Statement statement, Dictionary<string, string> rename)
        {
            if (statement == null) return;
            if (statement is AssignStmt)
            {
                statement = statement as AssignStmt;
                renameBody(((AssignStmt)statement).Lhs, rename);
                renameBody(((AssignStmt)statement).Rhs, rename);
            }
            else if (statement is UpdateStmt)
            {
                foreach (var st in ((UpdateStmt)statement).Rhss)
                {
                    renameBody(st, rename);
                }
                ((UpdateStmt)statement).Lhss.ForEach(x => renameBody(x, rename));
            }
            else if (statement is WhileStmt)
            {
                renameBody(((WhileStmt)statement).Body, rename);
                renameBody(((WhileStmt)statement).Guard, rename);
            }
            else if (statement is IfStmt)
            {
                renameBody(((IfStmt)statement).Guard, rename);
                renameBody(((IfStmt)statement).Thn, rename);
                renameBody(((IfStmt)statement).Els, rename);
            }
            else if (statement is BlockStmt)
            {
                foreach (var st in ((BlockStmt)statement).SubStatements)
                {
                    renameBody(st, rename);
                }
            }
            else if (statement is AssertStmt)
            {
                renameBody(((AssertStmt)statement).Expr, rename);
                renameBody(((AssertStmt)statement).Proof, rename);
            }
            else if (statement is VarDeclStmt)
            {
                if (((VarDeclStmt)statement).Update != null)
                    renameBody(((VarDeclStmt)statement).Update, rename);
                for(int i=0;i< ((VarDeclStmt)statement).Locals.Count; i++)
                {
                    var temp = ((VarDeclStmt)statement).Locals[i];
                    if (rename.ContainsKey(temp.Name)) ((VarDeclStmt)statement).Locals[i] = new LocalVariable(temp.Tok,temp.EndTok,rename[temp.Name],temp.Type,temp.IsGhost);
                }
            }
            else if (statement is CallStmt)
            {
                foreach (var expr in ((CallStmt)statement).Lhs)
                {
                    renameBody(expr, rename);
                }
                foreach (var expr in ((CallStmt)statement).Args)
                {
                    renameBody(expr, rename);
                }
            }
            else if (statement is PrintStmt)
            {
                foreach (var expr in ((PrintStmt)statement).Args)
                {
                    renameBody(expr, rename);
                }
            }
            else if (statement is AssignSuchThatStmt)
            {
                foreach (var expr in ((AssignSuchThatStmt)statement).Lhss)
                {
                    renameBody(expr, rename);
                }
                renameBody(((AssignSuchThatStmt)statement).Expr, rename);
            }
            else if (statement is CalcStmt)
            {
                // throw new NotImplementedException(statement.ToString());
                foreach (var x in ((CalcStmt)statement).Hints)
                {
                    renameBody(x, rename);
                }
                foreach (var x in ((CalcStmt)statement).Lines)
                {
                    renameBody(x, rename);
                }
                foreach (var x in ((CalcStmt)statement).Steps)
                {
                    renameBody(x, rename);
                }
            }
            else
            {
                throw new NotImplementedException(statement.ToString());
            }
        }
        public static void renameBody(Microsoft.Dafny.Expression expr, Dictionary<string, string> rename)
        {
            if (expr == null) return;
            if (expr is ApplySuffix)
            {
                List<Microsoft.Dafny.Expression> x = new List<Microsoft.Dafny.Expression>(((ApplySuffix)expr).Args);
                x.ForEach(m => renameBody(m, rename));
                expr = new ApplySuffix(expr.tok, ((ApplySuffix)expr).Lhs, x);
            }
            else if (expr is NameSegment)
            {
                //if (rename.ContainsKey(((NameSegment)expr).Name)) ((NameSegment)expr).Name = rename[((NameSegment)expr).Name];
            }
            else if (expr is BinaryExpr)
            {
                renameBody(((BinaryExpr)expr).E0, rename);
                renameBody(((BinaryExpr)expr).E1, rename);
            }
            else if (expr is UnaryExpr)
            {
                renameBody(((UnaryExpr)expr).E, rename);
            }
            else if (expr is ChainingExpression)
            {
                renameBody(((ChainingExpression)expr).E, rename);
            }
            else if (expr is SeqSelectExpr)
            {
                renameBody(((SeqSelectExpr)expr).Seq, rename);
                renameBody(((SeqSelectExpr)expr).E0, rename);
                renameBody(((SeqSelectExpr)expr).E1, rename);
            }
            else if (expr is ParensExpression)
            {
                renameBody(((ParensExpression)expr).E, rename);
            }
            else if (expr is SeqDisplayExpr)
            {
                foreach (Microsoft.Dafny.Expression x in ((SeqDisplayExpr)expr).Elements)
                {
                    renameBody(x, rename);
                }
            }
        }

        public static void renameBody(MaybeFreeExpression exp, Dictionary<string, string> rename)
        {
            renameBody(((MaybeFreeExpression)exp).E, rename);
        }



        public static void renameBody(AssignmentRhs Expr, Dictionary<string, string> rename)
        {
            if (Expr is ExprRhs)
            {
                renameBody(((ExprRhs)Expr).Expr, rename);
            }
        }

        public static Method FindMethod(string filename, string methodName, Microsoft.Dafny.Type[] InTypes, Microsoft.Dafny.Type[] retTypes)
        {
            // This was commented since it was causing verification to crash. (Boogie is likely to be the source)
            // DafnyOptions.Install(new DafnyOptions());

            var program = GetProgram(filename);
            var decls = program.Modules().SelectMany(m => m.TopLevelDecls).ToList();
            var callables = ModuleDefinition.AllCallables(decls);


            foreach (var currMethod in callables)
            {
                if (currMethod is Method)
                {
                    Boolean isFit = true;
                    if (((Method)currMethod).Name.Equals(methodName) && ((Method)currMethod).Ins.Count == InTypes.Length && ((Method)currMethod).Outs.Count == retTypes.Length)
                    {
                        for (int i = 0; i < InTypes.Length && isFit; i++)
                        {
                            if (!InTypes[i].Equals(((Method)currMethod).Ins[i].Type)) isFit = false;
                        }
                        for (int i = 0; i < retTypes.Length && isFit; i++)
                        {
                            if (!retTypes[i].Equals(((Method)currMethod).Outs[i].Type)) isFit = false;
                        }
                    }
                    else isFit = false;

                    if (isFit) return (Method)currMethod;
                }
            }
            return null;

            //var method = callables.Where(c => c is Method
            //    && ((Method)c).Name.Equals(methodName));


            //if (method.Any())
            //{
            //    return method.First() as Method;
            //}
            //else
            //{
            //    return null;
            //}
        }
        //laddon
        public static IWpfTextView GetWpfView()
        {
            var textManager = (IVsTextManager)ExtractMethodPackage.GetGlobalService(typeof(SVsTextManager));
            var componentModel = (IComponentModel)ExtractMethodPackage.GetGlobalService(typeof(SComponentModel));
            var editor = componentModel.GetService<IVsEditorAdaptersFactoryService>();
            IVsTextView textViewCurrent;
            textManager.GetActiveView(1, null, out textViewCurrent);
            return editor.GetWpfTextView(textViewCurrent);
        }

        //laddon
        public static Method GetCurrentMethod()
        {
            DTE dte = (DTE)ExtractMethodPackage.GetGlobalService(typeof(DTE));
            var fileName = dte.ActiveDocument.FullName;
            var textView = GetWpfView();
            //var x=textView.Selection.Start.Position;
            var caretPosition = textView.Caret.Position.BufferPosition.Position;
            return FindMethod(fileName, caretPosition);
        }

        public static string toDeclareString(List<DVariable> vars)
        {
            if (vars.Count == 0) return "";
            StringBuilder res = new StringBuilder();
            res.Append("var ");
            foreach (var x in vars)
            {
                res.Append(x.name + ": " + x.type + ", ");
            }
            res.Remove(res.Length - 2, 2);
            res.Append(";\r\n");
            return res.ToString();
        }

        public static List<AssertStmt> getPreAsserts(List<Statement> statements)
        {
            List<AssertStmt> res = new List<AssertStmt>();
            foreach (var st in statements)
            {
                if (st is AssertStmt)
                {
                    if(((AssertStmt)st).Proof==null)res.Add(st as AssertStmt);
                }
                else break;
            }
            return res;
        }

        public static List<Statement> removeReqAndEnsFromStmts(List<Statement> selected)
        {
            var temp = selected.ToList();
            foreach (var st in selected)
            {
                if (st is AssertStmt)
                {
                    if (((AssertStmt)st).Proof == null) temp.Remove(st);
                }
                else break;
            }
            var arr = temp.ToArray<Statement>();
            for (int i = arr.Length - 1; i >= 0; i--)
            {
                if (arr[i] is AssertStmt)
                {
                    if (((AssertStmt)arr[i]).Proof == null) temp.Remove(arr[i]);
                }
                else break;
            }
            return temp;
        }

        public static List<Statement> removeVarDeclFromStmts(List<Statement> selected)
        {
            var temp = selected.ToList();
            foreach (var st in selected)
            {
                if (st is VarDeclStmt) temp.Remove(st);
            }
            return temp;
        }

        public static String generateMethodCall(Method m, List<DVariable> args,List<DVariable> Lhs)
        {
            StringBuilder res = new StringBuilder();
            foreach(var x in Lhs)
            {
                res.Append(x.name);
                res.Append(", ");
            }
            if(Lhs.Count>0)res.Remove(res.Length - 2, 2);
            if(Lhs.Count>0)res.Append(" := ");
            res.Append(m.Name);
            res.Append("(");
            foreach (var x in args)
            {
                res.Append(x.name);
                res.Append(", ");
            }
            if(args.Count>0)res.Remove(res.Length - 2, 2);
            res.Append(");\r\n");
            return res.ToString();
        }


        public static List<AssertStmt> getPostAsserts(List<Statement> statements)
        {
            List<AssertStmt> res = new List<AssertStmt>();
            var arr = statements.ToArray<Statement>();
            for (int i = arr.Length - 1; i >= 0; i--)
            {
                if (arr[i] is AssertStmt)
                {
                    if (((AssertStmt)arr[i]).Proof == null) res.Add(arr[i] as AssertStmt);
                }
                else break;
            }
            return res;
        }
        //laddon
        public static Microsoft.Dafny.Program GetProgram(string filename)
        {
            List<DafnyFile> dafnyFiles = new List<DafnyFile>();
            dafnyFiles.Add(new DafnyFile(filename));
            ErrorReporter reporter = new ConsoleErrorReporter();
            Microsoft.Dafny.Program ret;
            Main.ParseCheck(dafnyFiles, filename, reporter, out ret);
            return ret;
        }
        //laddon
        public static IEnumerable<Statement> GetSelectedStatements()
        {
           
           
            var textView = GetWpfView();
            var start = textView.Selection.Start.Position.Position;
            var end = textView.Selection.End.Position.Position;
            // Get the highest-level statements in the method.
            var methodStatements = GetCurrentMethod().Body.SubStatements;
            // Invoke the recursive method on the highest-level statements in the current method.
            SelectionScope = GetCurrentMethod().Body;
            List<Statement> selected = GetSelectedStatementsRecursive(methodStatements, start, end);
            return selected;
        }
        //laddon
        public static List<Statement> GetSelectedStatementsRecursive(IEnumerable<Statement> statements, int start, int end)
        {
            List<Statement> selected = new List<Statement>();

            // Run over all the method's statements and retrieve the selected statements only.
            // Block statements (such as while, if, etc...) recieve special care.
            foreach (var s in statements)
            {
                if (s is WhileStmt)
                {
                    WhileStmt w = s as WhileStmt;

                    // If the while loop guard is grabbed by the selection, we consider the entire loop in.
                    if (IsExpressionInRange(w.Guard, start, end))
                        selected.Add(s);
                    else
                    {
                        if (s.Tok.pos < start && end < s.EndTok.pos)
                        {
                            SelectionScope = s;
                        }

                        selected.AddRange
                        (
                            GetSelectedStatementsRecursive(w.SubStatements.First().SubStatements, start, end)
                        );
                    }
                }
                else if (s is IfStmt)
                {
                    // For now we can only grab an entire "if/else" clause, along with all "if else" clauses,
                    // but not individual statements WITHIN any of the clauses.
                    // TODO: Support individual statements within an "if", "if else" or "else" clause.
                    IfStmt i = s as IfStmt;
                    if (IsExpressionInRange(i.Guard, start, end))
                        selected.Add(s);
                    else
                    {
                        if (s.Tok.pos < start && end < s.EndTok.pos)
                        {
                            SelectionScope = s;
                        }

                        selected.AddRange
                        (
                            GetSelectedStatementsRecursive(i.Thn.SubStatements, start, end)
                        );

                        if (i.Els is IfStmt) // i.Els represents "else if"
                        {
                            selected.AddRange
                            (
                                GetSelectedStatementsRecursive(new List<Statement> { i.Els }, start, end)
                            );
                        }
                        else if (i.Els is BlockStmt) // i.Els represents "else"
                        {
                            selected.AddRange
                            (
                                GetSelectedStatementsRecursive(i.Els.SubStatements, start, end)
                            );
                        }
                    }
                }
                else if (s is AlternativeStmt)
                {
                    if (IsExpressionInRange(s.SubExpressions.First(), start, end))
                        selected.Add(s);
                    else
                    {
                        SelectionScope = s;

                        foreach (Statement block in s.SubStatements)
                        {
                            selected.AddRange
                            (
                                GetSelectedStatementsRecursive(block.SubStatements, start, end)
                            );
                        }
                    }
                }
                else if (s is BlockStmt)
                {
                    if (IsStatementInRange(s, start, end))
                    {
                        if (s.Tok.pos < start && end < s.EndTok.pos)
                        {
                            SelectionScope = s;

                            selected.AddRange
                            (
                                GetSelectedStatementsRecursive(s.SubStatements, start, end)
                            );
                        }
                        else
                        {
                            selected.Add(s);
                        }
                    }
                }
                else
                {
                    if (IsStatementInRange(s, start, end))
                        selected.Add(s);
                }
            }

            return selected;
        }
        public static bool IsExpressionInRange(Microsoft.Dafny.Expression e, int start, int end)
        {
            return (e.tok.pos >= start && e.tok.pos <= end);
        }

        public static bool IsStatementInRange(Statement s, int start, int end)
        {
            return ((s.Tok.pos <= start && s.EndTok.pos >= start) ||
                    (s.Tok.pos <= end && s.EndTok.pos >= end) ||
                    (s.Tok.pos >= start && s.EndTok.pos <= end) ||
                    (s.Tok.pos <= start && s.EndTok.pos >= end));
        }



    }
}
