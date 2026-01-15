package analysis.fact;

import sootup.core.jimple.basic.Local;
import sootup.core.signatures.FieldSignature;
import sootup.core.types.NullType;

public class DataFlowFact {
    private static final DataFlowFact ZERO = new DataFlowFact(new Local("<ZERO>", NullType.getInstance()), null);
    private final Local variable;
    private final FieldSignature field;

    /**
     * Use this constructor for the dataflow analysis in Exercise 1.
     *
     * @param variable the Jimple local that contains tainted information
     */
    public DataFlowFact(Local variable) {
        this(variable, null);
    }

    /**
     * Use this constructor for the fieldSignature-based dataflow analysis in Exercise 2.
     *
     * @param fieldSignature the soot fieldSignature that receives a tainted data-flow.
     */
    public DataFlowFact(FieldSignature fieldSignature) {
        //A fieldSignature-based data flow fact has a local variable "FIELDBASED" as base. This is a dummy local variable that we construct here.
        this(new Local("FIELDBASED", fieldSignature.getType()), fieldSignature);
    }

    /**
     * Use this constructor for the field-sensitive dataflow analysis of Exercise 3.
     *
     * @param variable       the base variable at a field write statement that receives the taint.
     * @param fieldSignature the soot field that receives a tainted data-flow.
     */
    public DataFlowFact(Local variable, FieldSignature fieldSignature) {
        this.variable = variable;
        this.field = fieldSignature;
    }

    public static DataFlowFact getZeroInstance() {
        return ZERO;
    }

    public Local getVariable() {
        return variable;
    }

    public FieldSignature getFieldSignature() {
        return field;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((field == null) ? 0 : field.hashCode());
        result = prime * result + ((variable == null) ? 0 : variable.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        DataFlowFact other = (DataFlowFact) obj;
        if (field == null) {
            if (other.field != null)
                return false;
        } else if (!field.equals(other.field))
            return false;
        if (variable == null) {
            return other.variable == null;
        } else return variable.equals(other.variable);
    }

    @Override
    public String toString() {
        return variable + (field == null ? "" : " " + field);
    }

}
