using EnvDTE;
using Microsoft.Dafny;
using Microsoft.VisualStudio.Text;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Navigation;
using System.Windows.Shapes;

namespace Extract_Inline_Method
{
    /// <summary>
    /// Interaction logic for ExtractLemmaWindow.xaml
    /// </summary>
    public partial class ExtractLemmaWindow : System.Windows.Window
    {
        public ExtractLemmaWindow()
        {
            InitializeComponent();
        }
        private void button_Click(object sender, RoutedEventArgs e)
        {
            this.Hide();
            DVariableComparer comparer = new DVariableComparer();
            List<Statement> afterSelected;
            List<Statement> selectedStatements = (List<Statement>)HelpFunctions.GetSelectedStatements();
            if (selectedStatements.Count == 0) return;

            //start and end of all relevant stmts and not only the selected ones.
            var start = selectedStatements[0].Tok.pos;
            if (selectedStatements[0] is UpdateStmt)
            {
                if (((UpdateStmt)selectedStatements[0]).Lhss.Count > 0)
                    start = ((UpdateStmt)selectedStatements[0]).Lhss[0].tok.pos;
                else if (((UpdateStmt)selectedStatements[0]).Rhss.Count > 0)
                {
                    if (((UpdateStmt)selectedStatements[0]).Rhss[0] is ExprRhs)
                    {
                        if (((ExprRhs)((UpdateStmt)selectedStatements[0]).Rhss[0]).Expr is ApplySuffix)
                        {
                            start -= ((NameSegment)((ApplySuffix)((ExprRhs)((UpdateStmt)selectedStatements[0]).Rhss[0]).Expr).Lhs).Name.Length;
                        }
                    }
                }
            }
            var end = selectedStatements[selectedStatements.Count - 1].EndTok.pos;

            HelpFunctions.GetSelectedStatements(out afterSelected).ToList();
            List<DVariable> tempIns = new List<DVariable>();
            List<DVariable> tempOuts = new List<DVariable>();
            List<DVariable> tempToDeclare = new List<DVariable>();
            HelpFunctions.GetVariables(selectedStatements, afterSelected, out tempIns, out tempOuts, out tempToDeclare);
            tempOuts = new List<DVariable>();//because lemma has no return!!!!!!!!!
            List<DVariable> intersect = tempIns.Intersect(tempOuts, comparer).ToList<DVariable>();
            Dictionary<string, string> renameDic = new Dictionary<string, string>();
            foreach (var x in intersect)
            {
                renameDic.Add(x.name, x.name + "0");
            }
            List<Formal> ins = new List<Formal>();
            List<Formal> outs = new List<Formal>();

            foreach (var x in tempIns)
            {
                DVariable temp = new DVariable(x.name, x.type);
                if (renameDic.ContainsKey(temp.name)) temp.name = renameDic[temp.name];
                ins.Add(temp.ToFormal());
            }

            foreach (var x in tempOuts)
            {
                outs.Add(x.ToFormal());
            }


            var requires = HelpFunctions.getPreAsserts(selectedStatements);
            var ensures = HelpFunctions.getPostAsserts(selectedStatements);
            selectedStatements = HelpFunctions.removeReqAndEnsFromStmts(selectedStatements);
            selectedStatements = HelpFunctions.removeVarDeclFromStmts(selectedStatements);
            var method = HelpFunctions.GetCurrentMethod();
            List<MaybeFreeExpression> req = new List<MaybeFreeExpression>();
            foreach (var x in requires)
            {
                //HelpFunctions.renameBody(x.Expr, renameDic);
                req.Add(new MaybeFreeExpression(HelpFunctions.renameB(x.Expr,renameDic)));
            }
            List<MaybeFreeExpression> ens = new List<MaybeFreeExpression>();
            foreach (var x in ensures)
            {
                ens.Add(new MaybeFreeExpression(x.Expr));
            }
            var newMethod = new Lemma(null, this.textBox.Text, false, new List<TypeParameter>(), ins, outs, req, new Specification<FrameExpression>(null, null), ens, new Specification<Microsoft.Dafny.Expression>(null, null), null, null, null);
            //var newMethod = new Method(null, this.textBox.Text, false, false, new List<TypeParameter>(), ins, outs, req, new Specification<FrameExpression>(null, null), ens, new Specification<Microsoft.Dafny.Expression>(null, null), null, null, null);
            List<Microsoft.Dafny.Expression> Lhs = new List<Microsoft.Dafny.Expression>();
            List<AssignmentRhs> Rhs = new List<AssignmentRhs>();
            foreach (var x in intersect)
            {
                Lhs.Add(new NameSegment(null, x.name, new List<Microsoft.Dafny.Type>()));
                Rhs.Add(new ExprRhs(new NameSegment(null, x.name + "0", new List<Microsoft.Dafny.Type>())));
            }
            if (Lhs.Count > 0)
            {
                UpdateStmt correctingNames = new UpdateStmt(null, null, Lhs, Rhs);
                selectedStatements.Insert(0, correctingNames);
            }
            newMethod.Body = new BlockStmt(null,null, selectedStatements);
            string signature = Printer.MethodSignatureToString(newMethod);
            string body = Printer.StatementToString(newMethod.Body);
            // Place the new method implementation in the code.
            int position = HelpFunctions.GetCurrentMethod().BodyEndTok.pos + 1;
            ITextEdit edit = HelpFunctions.GetWpfView().TextBuffer.CreateEdit();
            edit.Insert(position, "\r\n\r\n" + signature + "\r\n" + body);

            string methodcall = HelpFunctions.generateMethodCall(newMethod, tempIns, tempOuts);
            //DTE dte = (DTE)ExtractMethodPackage.GetGlobalService(typeof(DTE));
            //var selection = (EnvDTE.TextSelection)dte.ActiveDocument.Selection;

            edit.Delete(start, end - start + 1);
            edit.Insert(start, HelpFunctions.toDeclareString(tempToDeclare) + methodcall);
            edit.Apply();
            //selection.Text = methodcall;
        }
    }
}
