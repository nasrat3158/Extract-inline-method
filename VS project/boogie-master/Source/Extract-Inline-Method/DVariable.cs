using Microsoft.Dafny;

namespace Extract_Inline_Method
{
    class DVariable
    {
        public string name;
        public Type type;

        public DVariable(string name, Type type) 
        {
            //if (type == null) throw new Exception("Dvariable with no type!!!!!");
            this.name = name;
            this.type = type;
        }

        public Formal ToFormal()
        {
            return new Microsoft.Dafny.Formal(null, name, type, false, false);
        }

        public override string ToString()
        {
            return name+" "+type;
        }


    }

}
