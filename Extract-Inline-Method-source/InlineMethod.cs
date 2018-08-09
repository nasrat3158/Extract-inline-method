//------------------------------------------------------------------------------
// <copyright file="InlineMethod.cs" company="Company">
//     Copyright (c) Company.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

using System;
using System.ComponentModel.Design;
using System.Globalization;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.Dafny;
using EnvDTE;
using System.Collections.Generic;
using System.Text;
using System.Linq;
using Microsoft.VisualStudio.Text;
using System.IO;

namespace Extract_Inline_Method
{
    /// <summary>
    /// Command handler
    /// </summary>
    internal sealed class InlineMethod
    {
        /// <summary>
        /// Command ID.
        /// </summary>
        public const int CommandId = 4129;

        /// <summary>
        /// Command menu group (command set GUID).
        /// </summary>
        public static readonly Guid CommandSet = new Guid("06ea6d48-60e4-4478-9f70-ac0ba610b2ff");

        /// <summary>
        /// VS Package that provides this command, not null.
        /// </summary>
        private readonly Package package;
        private static ITextEdit edit;
        /// <summary>
        /// Initializes a new instance of the <see cref="InlineMethod"/> class.
        /// Adds our command handlers for menu (commands must exist in the command table file)
        /// </summary>
        /// <param name="package">Owner package, not null.</param>
        private InlineMethod(Package package)
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
        public static InlineMethod Instance
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the service provider from the owner package.
        /// </summary>
        public IServiceProvider ServiceProvider
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
            Instance = new InlineMethod(package);
        }
        public static Microsoft.Dafny.Type[] getTypes(List<Microsoft.Dafny.Expression> expressions)
        {
            Microsoft.Dafny.Type[] Types = new Microsoft.Dafny.Type[expressions.Count];
            int index = 0;
            foreach (var x in expressions)
            {
                Types[index++] = x.Type;
            }
            return Types;
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
            DTE dte = (DTE)this.ServiceProvider.GetService(typeof(DTE));
            dte.ActiveDocument.Save();
            var fileName = dte.ActiveDocument.FullName;
            var selectedStatements = (List<Statement>)HelpFunctions.GetSelectedStatements();
            if (selectedStatements.Count == 1 && selectedStatements[0] is UpdateStmt)
            {
                UpdateStmt curr = (UpdateStmt)selectedStatements[0];
                var arg = ((ApplySuffix)((ExprRhs)curr.Rhss[0]).Expr).Args;
                Microsoft.Dafny.Type[] InTypes = getTypes(arg);

                var rets = curr.Lhss;
                Microsoft.Dafny.Type[] retTypes = getTypes(rets);

                Method m = HelpFunctions.FindMethod(fileName, ((NameSegment)((ApplySuffix)((ExprRhs)curr.Rhss[0]).Expr).Lhs).Name, InTypes, retTypes);
                edit = HelpFunctions.GetWpfView().TextBuffer.CreateEdit();
                inline(curr, fileName, m);
                edit.Apply();
                ////////////////////////////////////
                
            }
            else if (selectedStatements.Count == 0 && HelpFunctions.GetCurrentMethod() != null)
            {
                Method currMethod = HelpFunctions.GetCurrentMethod();

                var program = HelpFunctions.GetProgram(fileName);
                var decls = program.Modules().SelectMany(m => m.TopLevelDecls).ToList();
                var callables = ModuleDefinition.AllCallables(decls);
                edit = HelpFunctions.GetWpfView().TextBuffer.CreateEdit();
                foreach (var curr in callables)
                {
                    if (curr is Method)
                    {
                        var m = curr as Method;
                        traverse(m.Body, currMethod);
                    }
                }
                var textView = HelpFunctions.GetWpfView();
                var start = currMethod.tok.pos;
                if (currMethod is Lemma) start -= 6;
                else start -= 7;
                var end = currMethod.BodyEndTok.pos+1;
                edit.Delete(start,end-start);
                edit.Apply();
                
            }
            //HelpFunctions.prettyPrint(fileName);
        }
        public static void traverse(Statement statement, Method m)
        {
            if (statement is AssignStmt)
            {
                statement = statement as AssignStmt;
                traverse(((AssignStmt)statement).Lhs, m);
            }
            else if (statement is UpdateStmt)
            {
                DTE dte = (DTE)ExtractMethodPackage.GetGlobalService(typeof(DTE));
                var fileName = dte.ActiveDocument.FullName;

                UpdateStmt curr = (UpdateStmt)statement;
                if (!(((ExprRhs)curr.Rhss[0]).Expr is ApplySuffix)) return;
                var arg = ((ApplySuffix)((ExprRhs)curr.Rhss[0]).Expr).Args;
                Microsoft.Dafny.Type[] InTypes = getTypes(arg);

                var rets = curr.Lhss;
                Microsoft.Dafny.Type[] retTypes = getTypes(rets);

                Method temp = HelpFunctions.FindMethod(fileName, ((NameSegment)((ApplySuffix)((ExprRhs)curr.Rhss[0]).Expr).Lhs).Name, InTypes, retTypes);

                //check name of called func first;
                if (MethodsAreEqual(m,temp)) inline((UpdateStmt)statement, fileName, m);
            }
            else if (statement is WhileStmt)
            {
                traverse(((WhileStmt)statement).Body, m);
                traverse(((WhileStmt)statement).Guard, m);
            }
            else if (statement is IfStmt)
            {
                traverse(((IfStmt)statement).Guard, m);
                traverse(((IfStmt)statement).Thn, m);
                traverse(((IfStmt)statement).Els, m);
            }
            else if (statement is BlockStmt)
            {
                foreach (var st in ((BlockStmt)statement).SubStatements)
                {
                    traverse(st, m);
                }
            }
            else if (statement is AssertStmt)
            {
                traverse(((AssertStmt)statement).Proof,m);
            }
            else if (statement is AlternativeStmt)
            {

            }
            else if (statement is VarDeclStmt)
            {
                if (((VarDeclStmt)statement).Update != null)
                    traverse(((VarDeclStmt)statement).Update, m);
                foreach (var localvar in ((VarDeclStmt)statement).Locals)
                {
                    //traverse(localvar);
                }
            }
            else if (statement is CallStmt)
            {
                foreach (var expr in ((CallStmt)statement).Lhs)
                {
                    traverse(expr, m);
                }
                foreach (var expr in ((CallStmt)statement).Args)
                {
                    traverse(expr, m);
                }
            }
            else if (statement is PrintStmt)
            {
                foreach (var expr in ((PrintStmt)statement).Args)
                {
                    traverse(expr, m);
                }
            }
            else if (statement is AssignSuchThatStmt)
            {
                foreach (var expr in ((AssignSuchThatStmt)statement).Lhss)
                {
                    traverse(expr, m);
                }
                traverse(((AssignSuchThatStmt)statement).Expr, m);
            }
            else if (statement is CalcStmt)
            {

            }
            else if (statement is MatchStmt)
            {

            }
            else
            {
                if(statement!=null)throw new NotImplementedException(statement.ToString());
            }
        }


        public static void traverse(Microsoft.Dafny.Expression expr, Method me)
        {
            if (expr == null) return;
            if (expr is ApplySuffix)
            {
                List<Microsoft.Dafny.Expression> x = new List<Microsoft.Dafny.Expression>(((ApplySuffix)expr).Args);
                x.ForEach(m => traverse(m, me));
                expr = new ApplySuffix(expr.tok, ((ApplySuffix)expr).Lhs, x);
            }
            else if (expr is NameSegment)
            {

            }
            else if (expr is BinaryExpr)
            {
                traverse(((BinaryExpr)expr).E0, me);
                traverse(((BinaryExpr)expr).E1, me);
            }
            else if (expr is UnaryExpr)
            {
                traverse(((UnaryExpr)expr).E, me);
            }
            else if (expr is ChainingExpression)
            {
                traverse(((ChainingExpression)expr).E, me);
            }
            else if (expr is SeqSelectExpr)
            {
                traverse(((SeqSelectExpr)expr).Seq, me);
                traverse(((SeqSelectExpr)expr).E0, me);
                traverse(((SeqSelectExpr)expr).E1, me);
            }
            else if (expr is ParensExpression)
            {
                traverse(((ParensExpression)expr).E, me);
            }
            else if (expr is SeqDisplayExpr)
            {
                foreach (Microsoft.Dafny.Expression x in ((SeqDisplayExpr)expr).Elements)
                {
                    traverse(x, me);
                }
            }
        }
        public static void inline(UpdateStmt stmt, string fileName, Method m/*the called method*/)
        {

            DTE dte = (DTE)ExtractMethodPackage.GetGlobalService(typeof(DTE));
            if (!(((ExprRhs)stmt.Rhss[0]).Expr is ApplySuffix)) return;
            //var arg = ((ApplySuffix)((ExprRhs)stmt.Rhss[0]).Expr).Args;
            //Microsoft.Dafny.Type[] InTypes = getTypes(arg);

            //var rets = stmt.Lhss;
            //Microsoft.Dafny.Type[] retTypes = getTypes(rets);

            //Method m = HelpFunctions.FindMethod(fileName, ((NameSegment)((ApplySuffix)((ExprRhs)stmt.Rhss[0]).Expr).Lhs).Name, InTypes, retTypes);
            //Method m = HelpFunctions.FindMethod(fileName, "MinAndMax");
            Dictionary<string, string> rename = new Dictionary<string, string>();
            List<Microsoft.Dafny.Expression> currArgs = ((ApplySuffix)((ExprRhs)stmt.Rhss[0]).Expr).Args;
            List<Microsoft.Dafny.Expression> currRet = stmt.Lhss;
            for (int i = 0; i < m.Ins.Count && i < currArgs.Count; i++)
            {
                if (currArgs[i] is Microsoft.Dafny.Expression)
                {
                    rename.Add(m.Ins[i].Name, Printer.ExprToString(currArgs[i]));
                }
                else throw new NotImplementedException();

            }
            for (int i = 0; i < m.Outs.Count && i < currRet.Count; i++)
            {
                rename.Add(m.Outs[i].Name, Printer.ExprToString(currRet[i]));
            }
            List<MaybeFreeExpression> Ens = new List<MaybeFreeExpression>(m.Ens);
            List<MaybeFreeExpression> Req = new List<MaybeFreeExpression>(m.Req);
            //foreach (var x in Ens)
            //{
            //    HelpFunctions.renameBody(x, rename);
            //    //ens.Add(new AssertStmt());
            //}

            StringBuilder res = new StringBuilder();
            int indentLength = (stmt.Tok.col- ((NameSegment)((ApplySuffix)((ExprRhs)stmt.Rhss[0]).Expr).Lhs).Name.Length) -1;
            if (stmt.Lhss.Count > 0) indentLength = stmt.Lhss[0].tok.col -1;
            string indent = new string('\t', indentLength);
            foreach (var x in Req)
            {
                //HelpFunctions.renameBody(x, rename);
                res.Append(indent+"assert " + Printer.ExprToString(HelpFunctions.renameB(x.E,rename)) + ";\r\n");
            }

            //HelpFunctions.renameBody(m.Body, rename);
            m.Body = (BlockStmt)HelpFunctions.renameB(m.Body, rename);

            foreach (var x in m.Body.Body)
            {
                res.Append(indent + Printer.StatementToString(x,indentLength*4) + "\r\n");
            }

            foreach (var x in Ens)
            {
                res.Append(indent + "assert " + Printer.ExprToString(HelpFunctions.renameB(x.E,rename)) + ";\r\n");
            }

            string result = res.ToString();
            if (Ens.Count > 0) result = result.Remove(result.Length - 2, 2);

            //ITextEdit edit = HelpFunctions.GetWpfView().TextBuffer.CreateEdit();
            int from = stmt.Tok.pos-m.Name.Length;
            if (stmt.Lhss.Count > 0) from = stmt.Lhss[0].tok.pos;
            edit.Delete(from, stmt.EndTok.pos - from + 1);
            if (result.Length > 1) edit.Insert(from, result.Substring(indentLength));
            //edit.Apply();
            //((EnvDTE.TextSelection)dte.ActiveDocument.Selection).Text = "";
            ////((EnvDTE.TextSelection)dte.ActiveDocument.Selection).Delete();
            //if (result.Length > 1) ((EnvDTE.TextSelection)dte.ActiveDocument.Selection).Insert(result.Substring(1));
        }
        public static Boolean MethodsAreEqual(Method first, Method second)
        {
            if (first == null || second == null) return false;
            if (!first.Name.Equals(second.Name)) return false;
            if (first.Ins.Count != second.Ins.Count) return false;
            if (first.Outs.Count != second.Outs.Count) return false;
            for(int i = 0; i < first.Ins.Count; i++)
            {
                if (!first.Ins[i].Type.Equals(second.Ins[i].Type)) return false;
            }

            for(int i = 0; i < first.Outs.Count; i++)
            {
                if (!first.Outs[i].Type.Equals(second.Outs[i].Type)) return false;
            }

            return true;
        }
    }
}
