import org.chocosolver.memory.IStateLong;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.extension.Tuples;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.solver.variables.impl.BitsetIntVarImpl;
import org.chocosolver.util.ESat;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.ArrayList;

public class TableFDEOri extends Propagator<BitsetIntVarImpl> {

    private ArrayList<BitSupport>[][] tempBitTable;
    private IStateLong[] bitVal;
    private boolean firstProp=true;
    protected Tuples tuples;
    protected int[] offset;
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;

    public TableFDEOri(BitsetIntVarImpl[] vars, Tuples tuples){
        super(vars, PropagatorPriority.QUADRATIC, false);
        this.tuples = tuples;
        this.computeSupports(tuples);
        this.monitors = new IIntDeltaMonitor[vars.length];                //应该是存储删值集合
        for(int i = 0; i < vars.length; ++i) {
            this.monitors[i] = vars[i].monitorDelta(this);
        }
        this.onValRem = this.makeProcedure();
    }
    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int var, off;

            @Override
            public UnaryIntProcedure set(Integer o) {
                var = o;
                off = offset[var];
                return this;
            }

            @Override
            public void execute(int i) throws ContradictionException {
                ArrayList<BitSupport> bitSup=tempBitTable[var][i-offset[var]];
                for(int j=0;j<bitSup.size();j++){
                    int ts=bitSup.get(j).ts;
                    long u=bitSup.get(j).mask&bitVal[ts].get();
                    if(u!=0L){
                        bitVal[ts].set(bitVal[ts].get()&~u);
                    }
                }
            }
        };
    }
    protected void computeSupports(Tuples tuples) {
        int nw = tuples.nbTuples() / 64;
        if (nw * 64 < tuples.nbTuples()) {
            ++nw;
        }
        bitVal=new IStateLong[nw];
        for(int i = 0; i < nw; ++i) {
            bitVal[i] = this.model.getEnvironment().makeLong(-1L);
        }
        int n = vars.length;
        offset = new int[n];
//        bitTables = new BitSupport[n][][];
        tempBitTable= new ArrayList[n][];
        int[] size=new int[n];
        long[] tmp;
        for (int i = 0; i < n; i++) {
            int lb = vars[i].getLB();
            int ub = vars[i].getUB();
            offset[i] = lb;
            size[i]=ub-lb+1;
//            bitTables[i] = new BitSupport[ub - lb + 1][];
            tempBitTable[i]=new ArrayList[ub - lb + 1];
        }
        for (int i = 0; i < n; i++) {
            for(int j=0;j<size[i];j++){
                tempBitTable[i][j]=new ArrayList<BitSupport>();
            }
        }

        int t=0;
        while (t<tuples.nbTuples()){
            if(isValidTuple(tuples.get(t))){
                int ts=t/64;
                int index=t%64;
                for(int i=0;i<n;i++){
                    int a=tuples.get(t)[i];
                    ArrayList<BitSupport> bitSupportsArray=tempBitTable[i][a];
                    int low=0;
                    int high=bitSupportsArray.size()-1;
                    int middle=0;
                    boolean find=false;
                    while (low <= high) {
                        middle = (low + high) / 2;
                        if (ts == bitSupportsArray.get(middle).ts) {
                            bitSupportsArray.get(middle).mask |= 1L<<(63-index);
                            find = true;
                            break;
                        } else if (ts < bitSupportsArray.get(middle).ts) {
                            high = middle - 1;
                        } else {
                            low = middle + 1;
                        }
                    }
                    if (!find) {
                        int loc = high + 1;
                        BitSupport bitSupport = new BitSupport(ts, 1L<<(63-index));
                        bitSupportsArray.add(bitSupport);
                    }
                }
            }
            t++;
        }

//        for (int i = 0; i < n; i++) {
//            for(int j=0;j<size[i];j++){
//                bitTables[i][j]=new BitSupport[tempBitTable[i][j].size()];
//                for(int k=0;k<tempBitTable[i][j].size();k++)
//                    bitTables[i][j][k]=tempBitTable[i][j].get(k);
//            }
//        }
    }

    private void deleteInvalid()throws ContradictionException{
        for(int i=0;i<vars.length;i++){
            monitors[i].freeze();
            if(monitors[i].sizeApproximation()>0){
//                System.out.println(monitors[i].sizeApproximation());
                monitors[i].forEachRemVal(onValRem.set(i));
            }
            monitors[i].unfreeze();
        }
    }

    private void searchSupport() throws ContradictionException {
        for(int i=0;i<vars.length;i++){
            int ub=vars[i].getUB();
//            System.out.println(vars[i].getUB()+"  "+vars[i].getLB());
            for(int v = vars[i].getLB(); v <= ub; v=vars[i].nextValue(v)){
                ArrayList<BitSupport> bitSup=tempBitTable[i][v-offset[i]];
                int now=findSupport(bitSup,bitVal);
                if(now==-1){
                    vars[i].removeValue(v, this);
                }
            }
        }
    }

    private int findSupport(ArrayList<BitSupport> bitSupports, IStateLong[] bitVal){
        int i=bitSupports.size()-1;
        while(i>=0){
            if ((bitSupports.get(i).mask & bitVal[bitSupports.get(i).ts].get()) != 0L) return i;
            i-=1;
        }
        return -1;
    }

    private void initialPropagate() throws ContradictionException {
        for (int i = 0; i < vars.length; i++) {
            for(int j=0;j<vars[i].getDomainSize();j++){
                if(tempBitTable[i][j].size()==0)
                    vars[i].removeValue(j,this);
            }
        }
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        if(firstProp){
            initialPropagate();
            firstProp=false;
        }
        deleteInvalid();
        searchSupport();
    }
    @Override
    public ESat isEntailed() {
        return tuples.check(vars);
    }

    private boolean isValidTuple(int[] tuple){
        for(int i = 0; i < vars.length ; i++){
            if(!vars[i].contains(tuple[i]))
                return false;
        }
        return true;
    }

    private class BitSupport{
        public int ts;
        public long mask;

        public BitSupport(int ts,Long mask){
            this.ts=ts;
            this.mask=mask;
        }
    }
}
