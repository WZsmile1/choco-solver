import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateInt;
import org.chocosolver.memory.IStateLong;
import org.chocosolver.memory.structure.S64BitSet2;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.extension.Tuples;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.solver.variables.impl.BitsetIntVarImpl;
import org.chocosolver.util.ESat;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.ArrayList;

public class TableFDEAdd extends Propagator<BitsetIntVarImpl> {

    RSparseBitSet currTable;
    protected Tuples tuples;
    protected long[][][] supports;
    int[][] residues;
    protected int[] offset;
    private str2_var str2vars[];
    private ArrayList<str2_var> Ssup;
    private ArrayList<str2_var> Sval;
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private S64BitSet2 s;

    public TableFDEAdd(BitsetIntVarImpl[] vars, Tuples tuples){
        super(vars, PropagatorPriority.QUADRATIC, false);
        this.tuples = tuples;
        this.currTable = new RSparseBitSet(this.model.getEnvironment(), this.tuples.nbTuples());
        this.computeSupports(tuples);
        str2vars = new str2_var[vars.length-1];
        for (int i = 0; i < vars.length-1; i++) {
            str2vars[i] = new str2_var(model.getEnvironment(), i);
        }
        Ssup = new ArrayList<>();
        Sval = new ArrayList<>();
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
                currTable.addToMask((supports[var][i - off]));
            }
        };
    }
    protected void computeSupports(Tuples tuples) {         //初始化support
        int n = vars.length-1;         //不要最后一个变量
        offset = new int[n+1];
        supports = new long[n][][];
        residues = new int[n][];
        long[] tmp;
        for (int i = 0; i < n; i++) {
            int lb = vars[i].getLB();
            int ub = vars[i].getUB();
            offset[i] = lb;
            supports[i] = new long[ub - lb + 1][currTable.words.length];
            residues[i] = new int[ub - lb + 1];
        }
        offset[n]=vars[n].getLB();
        int wI = 0;
        byte bI = 63;
        top:
        for (int ti = 0; ti < tuples.nbTuples(); ti++) {
            int[] tuple = tuples.get(ti);
            for (int i = 0; i < tuple.length-1; i++) {
                if (!vars[i].contains(tuple[i])) {
                    continue top;
                }
            }
            for (int i = 0; i < tuple.length-1; i++) {
                tmp = supports[i][tuple[i] - offset[i]];
                tmp[wI] |= 1L << (bI);
            }
            if (--bI < 0) {
                bI = 63;
                wI++;
            }
        }
    }
    @Override
    public void propagate(int evtmask) throws ContradictionException {
        Ssup.clear();
        Sval.clear();
        s=(S64BitSet2)this.vars[vars.length-1].VALUES;
        currTable.setWords(s.getWords());
        for (str2_var tmp : str2vars) {
            Ssup.add(tmp);
            if (tmp.last_size.get() != vars[tmp.var].getDomainSize()) {
                Sval.add(tmp);
                tmp.last_size.set(vars[tmp.var].getDomainSize());
            }
        }

        for(str2_var tmp : Sval){
            currTable.clearMask();
            monitors[tmp.var].freeze();
            if (vars[tmp.var].getDomainSize() > monitors[tmp.var].sizeApproximation()) {
                monitors[tmp.var].forEachRemVal(onValRem.set(tmp.var));
                currTable.reverseMask();
            } else {
                int ub = vars[tmp.var].getUB();
//                System.out.println(ub+"  "+vars[tmp.var].getLB());
                for (int v = vars[tmp.var].getLB(); v <= ub; v=vars[tmp.var].nextValue(v)) {
                    currTable.addToMask(supports[tmp.var][v - offset[tmp.var]]);
                }
            }
            currTable.intersectWithMask();
            monitors[tmp.var].unfreeze();
            if (currTable.isEmpty()) { // fail as soon as possible
                fails();
            }
        }
        if (currTable.isEmpty()) { // fail as soon as possible
            fails();
        }
        filterDomains();
        removevalues(vars.length-1);          //效率会低一些
//        s.setWords(currTable.getWords());
//        lastBoundFilter(vars.length-1);
        for(int i = 0; i < this.vars.length; ++i) {
            monitors[i].unfreeze();
        }
    }

    @Override
    public ESat isEntailed() {
        return tuples.check(vars);
    }
    private void removevalues(int i) throws ContradictionException {
        s=(S64BitSet2)vars[i].VALUES;
        IStateLong[] words=s.getWords();
        IStateLong[] currWords=currTable.getWords();
        for(int j=0;j<words.length;j++){
            long w1=words[j].get();
            long w2=currWords[j].get();
            if(w1!=w2){
                for(int k=63;k>=0;k--){
                    long mask=1L<<k;
                    if((w1&mask)!=(w2&mask)){
                        w1=w1&~mask;
                        vars[i].removeValue(j*64+63-k+offset[i],this);
                    }
                    if(w1==w2)
                        break;;
                }
            }
        }
    }
    private void lastBoundFilter(int i) throws ContradictionException {
        s=(S64BitSet2)vars[i].VALUES;
        int lb = vars[i].getLB();
        int ub = vars[i].getUB();
//        System.out.println(vars[i].getId()+" "+lb+"  "+ub+"  "+vars[i].getDomainSize());
        if (!s.get(lb)){
//            System.out.print(lb);
            lb=s.nextSetBit(lb-offset[i]);
//            System.out.println("   "+lb+"   "+vars[i].getUB());
            vars[i].updateLowerBound(lb+offset[i],this);
        }
        if(!s.get(ub)){
            ub=s.prevSetBit(ub-offset[i]);
            vars[i].updateUpperBound(ub+offset[i],this);
        }
    }

    private void filterDomains() throws ContradictionException {
        if (this.currTable.isEmpty()) {
            this.fails();
        }
        for(int i = 0; i < this.vars.length-1; ++i) {
            if (this.vars[i].hasEnumeratedDomain()) {
                this.enumFilter(i);
            } else {
                this.boundFilter(i);
            }
        }
    }

    private void boundFilter(int i) throws ContradictionException {
        int lb = vars[i].getLB();
        int ub = vars[i].getUB();
        for (int v = lb; v <= ub; v++) {
            int index = residues[i][v - offset[i]];
            if ((currTable.words[index].get() & supports[i][v - offset[i]][index]) == 0L) {
                index = currTable.intersectIndex(supports[i][v - offset[i]]);
                if (index == -1) {
                    lb++;
                } else {
                    residues[i][v - offset[i]] = index;
                    break;
                }
            } else {
                break;
            }
        }
        vars[i].updateLowerBound(lb, this);
        for (int v = ub; v >= ub; v--) {
            int index = residues[i][v - offset[i]];
            if ((currTable.words[index].get() & supports[i][v - offset[i]][index]) == 0L) {
                index = currTable.intersectIndex(supports[i][v - offset[i]]);
                if (index == -1) {
                    ub--;
                } else {
                    residues[i][v - offset[i]] = index;
                    break;
                }
            } else {
                break;
            }
        }
        vars[i].updateUpperBound(ub, this);
    }

    private void enumFilter(int i) throws ContradictionException {
        int ub = ((IntVar[])this.vars)[i].getUB();

        for(int v = ((IntVar[])this.vars)[i].getLB(); v <= ub; v = ((IntVar[])this.vars)[i].nextValue(v)) {
            int index = this.residues[i][v - this.offset[i]];
            if ((this.currTable.words[index].get() & this.supports[i][v - this.offset[i]][index]) == 0L) {
                index = this.currTable.intersectIndex(this.supports[i][v - this.offset[i]]);
                if (index == -1) {
                    ((IntVar[])this.vars)[i].removeValue(v, this);
                } else {
                    this.residues[i][v - this.offset[i]] = index;
                }
            }
        }

    }

    protected class RSparseBitSet {
        protected IStateLong[] words;
        private int[] index;
        private IStateInt limit;
        private long[] mask;

        protected RSparseBitSet(IEnvironment environment, int nbBits) {
            int nw = nbBits / 64;
            if (nw * 64 < nbBits) {
                ++nw;
            }
            this.index = new int[nw];
            this.mask = new long[nw];
            this.limit = environment.makeInt(nw - 1);
            this.words = new IStateLong[nw];

            for(int i = 0; i < nw; ++i) {
                this.index[i] = i;
                this.words[i] = environment.makeLong(-1L);
            }

        }

        protected void setWords(IStateLong[] w){
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                long word = this.words[offset].get() & w[offset].get();
                if (this.words[offset].get() != word) {
                    this.words[offset].set(word);
                    if (word == 0L) {
                        this.index[i] = this.index[this.limit.get()];
                        this.index[this.limit.get()] = offset;
                        this.limit.add(-1);
                    }
                }
            }
        }

        protected IStateLong[] getWords(){
            return words;
        }

        private boolean isEmpty() {
            return this.limit.get() == -1;
        }

        protected void clearMask() {
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                this.mask[offset] = 0L;
            }

        }

        protected void reverseMask() {
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                this.mask[offset] = ~this.mask[offset];
            }

        }

        protected void addToMask(long[] wordsToAdd) {
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                this.mask[offset] |= wordsToAdd[offset];
            }

        }

        private void intersectWithMask() {
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                long w = this.words[offset].get() & this.mask[offset];
                if (this.words[offset].get() != w) {
                    this.words[offset].set(w);
                    if (w == 0L) {
                        this.index[i] = this.index[this.limit.get()];
                        this.index[this.limit.get()] = offset;
                        this.limit.add(-1);
                    }
                }
            }

        }

        private int intersectIndex(long[] m) {
            for(int i = this.limit.get(); i >= 0; --i) {
                int offset = this.index[i];
                if ((this.words[offset].get() & m[offset]) != 0L) {
                    return offset;
                }
            }

            return -1;
        }

        public void show(){
            for (int i=0;i<=limit.get();i++) {
                System.out.printf("%x ", words[i].get());
                System.out.printf("%x \n", mask[i]);
            }
        }
    }

    private class str2_var {

        private int var;
        /**
         * original var
         */
        private IStateInt last_size;
        /**
         * Numerical reversible of the last size
         */

        private str2_var(IEnvironment env, int var_) {
            var = var_;
            last_size = env.makeInt(0);
        }
    }


}
