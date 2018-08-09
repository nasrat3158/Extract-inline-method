//------------------------------------------------------------------------------
// <copyright file="Command1.cs" company="Company">
//     Copyright (c) Company.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

using System;
using System.ComponentModel.Design;
using System.Globalization;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.Dafny;
using System.Collections.Generic;
using System.Linq;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.ComponentModelHost;
using Microsoft.VisualStudio.Editor;

namespace oneproject
{
    /// <summary>
    /// Command handler
    /// </summary>
    internal sealed class Command1
    {
        /// <summary>
        /// Command ID.
        /// </summary>
        public const int CommandId = 0x0100;

        /// <summary>
        /// Command menu group (command set GUID).
        /// </summary>
        public static readonly Guid CommandSet = new Guid("93397e01-1c66-4aeb-b900-376690e18336");

        /// <summary>
        /// VS Package that provides this command, not null.
        /// </summary>
        private readonly Package package;

        /// <summary>
        /// Initializes a new instance of the <see cref="Command1"/> class.
        /// Adds our command handlers for menu (commands must exist in the command table file)
        /// </summary>
        /// <param name="package">Owner package, not null.</param>
        private Command1(Package package)
        {
            if (package == null)
            {
                throw new ArgumentNullException("package");
            }

            this.package = package;

            OleMenuCommandService commandService = this.ServiceProvider.GetService(typeof(IMenuCommandService)) as OleMenuCommandService;
            if (commandService != null)
            {
                var menuCommandID = new CommandID(CommandSet, CommandId);
                var menuItem = new MenuCommand(this.MenuItemCallback, menuCommandID);
                commandService.AddCommand(menuItem);
            }
        }

        /// <summary>
        /// Gets the instance of the command.
        /// </summary>
        public static Command1 Instance
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the service provider from the owner package.
        /// </summary>
        private IServiceProvider ServiceProvider
        {
            get
            {
                return this.package;
            }
        }

        /// <summary>
        /// Initializes the singleton instance of the command.
        /// </summary>
        /// <param name="package">Owner package, not null.</param>
        public static void Initialize(Package package)
        {
            Instance = new Command1(package);
        }

        /// <summary>
        /// This function is the callback used to execute the command when the menu item is clicked.
        /// See the constructor to see how the menu item is associated with this function using
        /// OleMenuCommandService service and MenuCommand class.
        /// </summary>
        /// <param name="sender">Event sender.</param>
        /// <param name="e">Event args.</param>
        private void MenuItemCallback(object sender, EventArgs e)
        {
            string message = string.Format(CultureInfo.CurrentCulture, "Inside {0}.MenuItemCallback()", this.GetType().FullName);
            string title = "Command1";
            var textManager = this.ServiceProvider.GetService(typeof(SVsTextManager)) as IVsTextManager;
            IVsTextView textview;
            textManager.GetActiveView(1, null, out textview);
            var componentModel = this.ServiceProvider.GetService(typeof(SComponentModel)) as IComponentModel;
            var text = componentModel.GetService<IVsEditorAdaptersFactoryService>().GetWpfTextView(textview);
            int selection = text.Caret.Position.BufferPosition.Position;
            int end = text.Selection.End.Position;
            int start = text.Selection.Start.Position;
   
            //            addWhileStatement(text);
            // Show a message box to prove we were here
  /*          VsShellUtilities.ShowMessageBox(
                this.ServiceProvider,
                message,
                title,
                OLEMSGICON.OLEMSGICON_INFO,
                OLEMSGBUTTON.OLEMSGBUTTON_OK,
                OLEMSGDEFBUTTON.OLEMSGDEFBUTTON_FIRST);
*/
            string filename = "C:\\Users\\AboNezar\\Desktop\\Documents" +
                "\\Visual Studio 2015\\Projects\\ConsoleApplication5\\ConsoleApplication5\\test.dfy";
            Method m = FindMethod(filename, selection);
            List<Statement> other;
            var stmts=GetSelectedStatements(m, start, end,out other);
            List<DVariable> ins, outs, decs;
            GetVariables(stmts, other, out ins, out outs, out decs);

            AssertStmt preCond, postCond;
            GetConditions(m, selection, out preCond, out postCond);
                        HashSet<DVariable> d ;
                        var v=GetVars(m.Body.Body,out d);
            selection = m.BodyEndTok.pos+1;
            string s=buildMethod(preCond.ToString(), postCond.ToString());
            s = "\n"+num(m.Body.Body, new List<AssertStmt>(), new List<AssertStmt>())+"\n";
            var textService = this.ServiceProvider.GetService(typeof(EnvDTE._DTE)) as EnvDTE._DTE;
            //           var t = textService.ActiveDocument.Object() as EnvDTE.TextDocument;
            //           t.Selection.EndOfDocument();
            //           selection = text.Caret.Position.BufferPosition.Position;
            //WriteToTextViewer(s,text, selection);
            AssertStmt astmt= m.Body.Body[0] as AssertStmt;
            var exp = ExtractGuard(astmt.Expr);
        }

        public HashSet<DVariable> GetVars(List<Statement> statements, out HashSet<DVariable> declVars)
        {
            DVariableComparer comparer=new DVariableComparer();
            HashSet<DVariable> vars = new HashSet<DVariable>(comparer);
             declVars = new HashSet<DVariable>(comparer);
            foreach (var stmt in statements)
            {
                vars.UnionWith(GetVars(stmt, declVars));
            }

            return vars;
           
        }
        private HashSet<DVariable> GetVars(Statement stmt,HashSet<DVariable> declaredVars)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> usedVars = new HashSet<DVariable>(comparer);
            if(stmt is UpdateStmt)
            {
                var ustmt = (UpdateStmt)stmt;
                foreach(var ls in ustmt.Lhss)
                {
                    usedVars.UnionWith(GetVars(ls,declaredVars));
                }
                foreach (var rs in ustmt.Rhss)
                {
                    var exp = rs as ExprRhs;
                    usedVars.UnionWith(GetVars(exp.Expr, declaredVars));
                }
            }
            else if(stmt is AssertStmt)
            {
                var asrt = stmt as AssertStmt;
                usedVars.UnionWith(GetVars(asrt.Expr,declaredVars));
                usedVars.UnionWith(GetVars(asrt.Proof, declaredVars));

            }else if(stmt is WhileStmt)
            {
                var wstmt = stmt as WhileStmt;
                usedVars.UnionWith(GetVars(wstmt.Body,declaredVars));
                foreach(var exp in wstmt.Decreases.Expressions)
                      usedVars.UnionWith(GetVars(exp, declaredVars));
                usedVars.UnionWith(GetVars(wstmt.Guard, declaredVars));
                foreach (var exp in wstmt.Invariants)
                    usedVars.UnionWith(GetVars(exp.E, declaredVars));
            }
            else if(stmt is BlockStmt)
            {
                var stmts = stmt as BlockStmt;
                foreach (var bodyStmt in stmts.Body)
                {
                    usedVars.UnionWith(GetVars(bodyStmt,declaredVars));
                }

            }
            else if(stmt is VarDeclStmt)
            {
                var decl = stmt as VarDeclStmt;
                usedVars.UnionWith(GetVars(decl.Update, declaredVars));
                if (decl.Locals != null)
                {
                    foreach (var v in decl.Locals)
                    {
                        DVariable dvar = new DVariable(v.DisplayName, v.Type);
                        declaredVars.Add(dvar);
                    }
                }

            }
            else if(stmt is IfStmt)
            {
                var ifstmt = stmt as IfStmt;
                usedVars.UnionWith(GetVars(ifstmt.Guard, declaredVars));
                usedVars.UnionWith(GetVars(ifstmt.Thn, declaredVars));
                usedVars.UnionWith(GetVars(ifstmt.Els, declaredVars));
            }
            else if (stmt is PrintStmt)
            {
                var pstmt = stmt as PrintStmt;
                foreach(var arg in pstmt.Args)
                    usedVars.UnionWith(GetVars(arg, declaredVars));
            }

            return usedVars;
        }

        private HashSet<DVariable> GetVars(Expression exp,HashSet<DVariable> declaredVars)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> vars = new HashSet<DVariable>(comparer);
            if (exp is SeqSelectExpr)
            {
                var expr = exp as SeqSelectExpr;
                vars.UnionWith(GetVars(expr.Seq,declaredVars));
                vars.UnionWith(GetVars(expr.E0,declaredVars));
                vars.UnionWith(GetVars(expr.E1,declaredVars));
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
                foreach(var arg in expr.Args)
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
            else if (exp is ForallExpr)
            {
                var expr = exp as ForallExpr;
                var newDecVars = new HashSet<DVariable>(declaredVars,comparer);
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
        public void WriteToTextViewer(string codeToWrite,IWpfTextView viewer,int offset)
        {
            Microsoft.VisualStudio.Text.ITextEdit ie = viewer.Selection.TextView.TextBuffer.CreateEdit();
            ie.Insert(offset, codeToWrite);
            ie.Apply();
        }
        public void GetConditions(Method method, int offset, out AssertStmt preCond, out AssertStmt postCond)
        {
            List<Statement> body = method.Body.Body;
            List<Statement> lst = body.Where(m => m is AssertStmt).ToList();
            int max = int.MinValue;
            int min = int.MaxValue;
            preCond = null;
            postCond = null;
            foreach (var statement in lst)
            {
                if (statement.Tok.pos < offset)
                {
                    if (statement.Tok.pos - offset > max)
                    {
                        max = statement.Tok.pos - offset;
                        preCond = statement as AssertStmt;

                    }
                }
                else
                        if (offset - statement.Tok.pos < min)
                {
                    min = offset - statement.Tok.pos;
                    postCond = statement as AssertStmt;

                }
            }


        }


        public string num(List<Statement> selectedStatements,List<AssertStmt> requires, List<AssertStmt> ensures)
        {
            HashSet<DVariable> decl;
            HashSet<DVariable> vars = GetVars(selectedStatements, out decl);
            List<Formal> ins = new List<Formal>();
            foreach(var variable in vars)
            {
                ins.Add(variable.ToFormal());
            }
      //      var method = HelpFunctions.GetCurrentMethod();
            List<MaybeFreeExpression> req = new List<MaybeFreeExpression>();
            foreach (var x in requires)
            {
                req.Add(new MaybeFreeExpression(x.Expr));
            }
            List<MaybeFreeExpression> ens = new List<MaybeFreeExpression>();
            foreach (var x in ensures)
            {
                ens.Add(new MaybeFreeExpression(x.Expr));
            }
            
            var newMethod = new Method(null, "number", false, false, new List<TypeParameter>(), ins, new List<Formal>(), req, new Specification<FrameExpression>(null, null), ens, new Specification<Microsoft.Dafny.Expression>(null, null), null, null, null);
            newMethod.Body = new BlockStmt(selectedStatements.First().Tok, selectedStatements.Last().EndTok, selectedStatements);
            string ans= Printer.MethodSignatureToString(newMethod);
            Statement statement = new BlockStmt(null, null, selectedStatements);
            ans += Printer.StatementToString(statement);
            return ans;
        }

        public Expression ExtractGuard(Expression exp)
        {

            if (exp is BinaryExpr)
            {
                var expr = exp as BinaryExpr;
                if (expr.Op == BinaryExpr.Opcode.Eq)
                    return exp;
                var ans = ExtractGuard(expr.E0);
                if (ans == null)
                    return ExtractGuard(expr.E1);
                return ans;
            }
            else if (exp is UnaryOpExpr)
            {
                var expr = exp as UnaryOpExpr;
            }
            else if (exp is ParensExpression)
            {
                var expr = exp as ParensExpression;
                return ExtractGuard(expr.E);
            }
            else if (exp is ChainingExpression)
            {
                var expr = exp as ChainingExpression;
                return ExtractGuard(expr.E);
            }
            else if (exp is SeqDisplayExpr)
            {
                var expr = exp as SeqDisplayExpr;
                
            }
            return null;

        }

        public List<Statement> GetSelectedStatements(Method method,int start,int end,out List<Statement> otherStatements)
        {
            List<Statement> statements = new List<Statement>();
            otherStatements = new List<Statement>();
            foreach (var statement in method.Body.Body)
            {
                if (statement.Tok.pos >= start && statement.EndTok.pos <= end)
                    statements.Add(statement);
                else if (statement.Tok.pos > end)
                    otherStatements.Add(statement);

            }
            return statements;
        }

        public List<AssertStmt> GetRequires(List<Statement> statements)
        {
            List<AssertStmt> requires = new List<AssertStmt>();
            
            foreach(var stmt in statements)
            {
                if (stmt is AssertStmt)
                    requires.Add(stmt as AssertStmt);
                else return requires;
            }
            return requires;
        }

        public List<AssertStmt> GetEnsures(List<Statement> statements)
        {
            List<AssertStmt> ensures = new List<AssertStmt>();

            for (int i=statements.Count-1;i>-1;i--)
            {
                var stmt = statements[i];
                if (stmt is AssertStmt)
                    ensures.Add(stmt as AssertStmt);
                else return ensures;
            }
            return ensures;
        }

        public void GetVariables(List<Statement> statements,List<Statement> otherStatements,out List<DVariable> ins,out List<DVariable> outs,out List<DVariable> toDeclare)
        {
            DVariableComparer comparer = new DVariableComparer();
            HashSet<DVariable> varsDeclaredInSelectedScope;
            var varsUsedInSelectedScope = GetVars(statements, out varsDeclaredInSelectedScope);
            HashSet<DVariable> varsDeclaredAfterScope;
            var varsUsedAfterScope = GetVars(otherStatements, out varsDeclaredAfterScope);
            ins = varsUsedInSelectedScope.ToList();
            outs = varsUsedInSelectedScope.Intersect(varsUsedAfterScope,comparer).ToList();
            toDeclare = varsDeclaredInSelectedScope.Intersect(varsUsedAfterScope, comparer).ToList();
            //ins.AddRange(toDeclare);
        }
        public string buildMethod(string preCond,string postCond)
        {
         string methodName = "MMG_";
            string ins = "a0: nat";
            string outs = "a: nat";
            string method = "Method " + methodName + "( " + ins+ " ) returns ( "+outs+" )\n{\n";
            string body = "a=a0;";
            method += body+"\n}";

            
            
            return method;
        }
        public string GetNewName()
        {
            return null;
        }
        public List<string> getNames(string filename)
        {
            var program = getProgram(filename);
            List<TopLevelDecl> decls = new List<TopLevelDecl>();
            foreach (var module in program.Modules())
            {
                decls.AddRange(module.TopLevelDecls);
            }
            List<string> lst = new List<string>();
            var callables = ModuleDefinition.AllCallables(decls);
            foreach (var decl in callables)
            {
                if (decl is Method)
                    lst.Add(((Method)decl).Name);
                if (decl is Predicate)
                    lst.Add(((Predicate)decl).Name);
            }

            return lst;
        }


        public Program getProgram(string filename)
        {
            Program dafnyProgram;
            List<DafnyFile> dafnyFiles;
            List<string> otherFiles;
            string[] args = new string[] { filename };
            DafnyDriver.ProcessCommandLineArguments(args, out dafnyFiles, out otherFiles);
            ErrorReporter reporter = new ConsoleErrorReporter();
            Main.ParseCheck(dafnyFiles, "", reporter, out dafnyProgram);
            return dafnyProgram;
        }   

        public Method FindMethod(string filename, int offset)
        {

            var dafnyProgram = getProgram(filename);
            List<TopLevelDecl> decls = new List<TopLevelDecl>();
            foreach (var module in dafnyProgram.Modules())
            {
                decls.AddRange(module.TopLevelDecls);
            }
            var callables = ModuleDefinition.AllCallables(decls);
            var method = callables.Where(c => c is Method
                && ((Method)c).BodyStartTok.pos <= offset
                && ((Method)c).BodyEndTok.pos >= offset);
            ModuleDefinition.AllCallables(decls);
            if (method.Any())
                return method.First() as Method;
            else return null;

        }
        /*
         * schema:-
         *  while condition - 0
         *  invariant - 1
         *  precondition - 2
         *  postcondition - 3
         *  body - 4+
         */
        private void addWhileStatement(EnvDTE.TextDocument text)
        {
            string content = text.Selection.Text;
            string[] del = { "==", "<", ">", "!=", ">=", "<=" };
            string[] arr = content.Trim().Split('\n');
            string[] s = arr[0].Split(del, StringSplitOptions.RemoveEmptyEntries);
            string inv = "invariant " + arr[1].Trim() + "\n";
            string dec = "decreases " + s[1].Trim() + " - " + s[0].Trim();
            string pre = "\nassert " + arr[2].Trim('\n', '\r', ' ') + ";\n";
            string cond = "while (" + arr[0].Trim() + ")\n" + inv + dec + "\n{\n";
            string body = "";
            for (int i = 4; i < arr.Length; i++)
                body += arr[i];
            string post = "\n}\nassert " + arr[3].Trim('\r', '\n', ' ') + ";\n";

            //          text.CreateEditPoint(text.EndPoint).Insert(content);

            text.Selection.Text = pre + cond + body + post;
        }
    }
}

