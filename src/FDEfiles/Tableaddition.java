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
import org.chocosolver.solver.variables.events.PropagatorEventType;
import org.chocosolver.solver.variables.impl.BitsetIntVarImpl;
import org.chocosolver.util.ESat;
import org.chocosolver.util.procedure.UnaryIntProcedure;

public class Tableaddition extends Propagator<BitsetIntVarImpl> {
    Tableaddition.RSparseBitSet currTable;
    protected Tuples tuples;
    protected long[][][] supports;
    int[][] residues;
    protected int[] offset;
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private S64BitSet2 s;
    protected static final long WORD_MASK = 0xffffffffffffffffL;

    public Tableaddition(BitsetIntVarImpl[] vars, Tuples tuples) {
        super(vars, PropagatorPriority.QUADRATIC, true);
        this.tuples = tuples;
        this.currTable = new Tableaddition.RSparseBitSet(this.model.getEnvironment(), this.tuples.nbTuples());
        this.computeSupports(tuples);
        this.monitors = new IIntDeltaMonitor[vars.length-1];                //应该是存储删值集合
        for(int i = 0; i < vars.length-1; ++i) {
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
        int n = ((IntVar[])this.vars).length-1;         //不要最后一个变量
        this.offset = new int[n+1];
        this.supports = new long[n][][];
        this.residues = new int[n][];
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

    public void propagate(int evtmask) throws ContradictionException {
        s=(S64BitSet2)this.vars[vars.length-1].VALUES;
        currTable.setWords(s.getWords());
        if (PropagatorEventType.isFullPropagation(evtmask)) {
            for (int i = 0; i < vars.length-1; i++) {
                currTable.clearMask();
                int ub = vars[i].getUB();
                for (int v = vars[i].getLB(); v <= ub; v = vars[i].nextValue(v)) {
                    currTable.addToMask(supports[i][v - offset[i]]);
                }
                currTable.intersectWithMask();
            }
        }
        filterDomains();
        s.setWords(currTable.getWords());
        lastBoundFilter(vars.length-1);
        for(int i = 0; i < ((IntVar[])this.vars).length-1; ++i) {
            monitors[i].unfreeze();
        };
    }

    public void propagate(int vIdx, int mask) throws ContradictionException {
        if(vIdx==this.vars.length-1){

            s=(S64BitSet2)this.vars[vars.length-1].VALUES;
            currTable.setWords(s.getWords());
            forcePropagate(PropagatorEventType.CUSTOM_PROPAGATION);

        }else{
            s=(S64BitSet2)this.vars[vars.length-1].VALUES;
            currTable.setWords(s.getWords());
            currTable.clearMask();
            monitors[vIdx].freeze();
            if (vars[vIdx].getDomainSize() > monitors[vIdx].sizeApproximation()) {
                monitors[vIdx].forEachRemVal(onValRem.set(vIdx));
                currTable.reverseMask();
            } else {
                int ub = vars[vIdx].getUB();
                for (int v = vars[vIdx].getLB(); v <= ub; v = vars[vIdx].nextValue(v)) {
                    currTable.addToMask(supports[vIdx][v - offset[vIdx]]);
                }
            }
            currTable.intersectWithMask();
            monitors[vIdx].unfreeze();
            if (currTable.isEmpty()) { // fail as soon as possible
                fails();
            }
            s.setWords(currTable.getWords());
            lastBoundFilter(vars.length-1);
            forcePropagate(PropagatorEventType.CUSTOM_PROPAGATION);
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
    private void lastBoundFilter(int i) throws ContradictionException {
        s=(S64BitSet2)vars[i].VALUES;
        int lb = vars[i].getLB();
        int ub = vars[i].getUB();
//        System.out.println(vars[i].getId()+" "+lb+"  "+ub+"  "+vars[i].getDomainSize());
        if (!s.get(lb)){
            lb=s.nextSetBit(lb);
        }
        if(!s.get(ub)){
            ub=s.prevSetBit(ub);
        }
        vars[i].updateBounds(lb+offset[i],ub+offset[i], this);
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

    public ESat isEntailed() {
        // TODO optim : check current according to currTable?
        return tuples.check(vars);
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
            for(int i=0;i<w.length;i++)
                words[i].set(w[i].get());
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
}
