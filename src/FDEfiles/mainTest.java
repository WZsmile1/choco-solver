import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.extension.Tuples;
import org.chocosolver.solver.search.strategy.selectors.variables.ImpactBased;
import org.chocosolver.solver.variables.impl.BitsetIntVarImpl;

public class mainTest {

    public static void main(String[] args) throws Exception {
        String[] path ={ "D:\\optiSTRpackage\\rand-8-20-5_total20\\rand-8-20-5-18-800-1_ext.xml",
                "D:\\optiSTRpackage\\dubois\\normalized-dubois-20_ext.xml",
                "D:\\optiSTRpackage\\X2Bench\\modifiedRenault_600s26\\renault-mod-0_ext.xml",
                "D:\\optiSTRpackage\\aim-50_total24\\aim-50-1-6-sat-1_ext.xml",
                "D:\\optiSTRpackage\\aim-100_part17\\aim-100-2-0-sat-1_ext.xml",
                "D:\\optiSTRpackage\\aim-200_600s8\\aim-200-3-4-sat-1_ext.xml",
                "D:\\optiSTRpackage\\rand-10-60-20_600s32\\rand-10-60-20-30-p51200-0_ext_glb.xml",
                "D:\\optiSTRpackage\\rand-3-20-20_total50\\rand-3-20-20-60-632-1_ext.xml",
                "D:\\optiSTRpackage\\rand-3-20-20-fcd_total50\\rand-3-20-20-60-632-fcd-1_ext.xml",
                "D:\\optiSTRpackage\\rand-3-24-24_600s15\\rand-3-24-24-76-632-1_ext.xml",
                "D:\\optiSTRpackage\\rand-3-24-24-fcd_600s17\\rand-3-24-24-76-632-fcd-1_ext.xml",
                "D:\\optiSTRpackage\\aarand-10-20-10_total20\\rand-10-20-10-5-10000-0_ext.xml",
                "D:\\optiSTRpackage\\rand-5-12-12_total50\\rand-5-12-12-200-p12442-1_ext_glb.xml",
                "D:\\java\\ScalaCP\\benchmarks\\test2.xml",
                "D:\\optiSTRpackage\\csptools\\rand-4-10-5-10-800-fcd-1_ext-merged.xml",
                "D:\\optiSTRpackage\\travellingSalesman-20_total15\\tsp-20-1_ext.xml"};
        int fmt=2;
//        for(int i=1;i<12;i++){
//            solve(path[i],fmt);
//        }
        solve(path[0],fmt);
        solve2(path[0],fmt);

    }

    public static void solve(String Path,int format) throws Exception {
        //        XModel xm=new XModel(Path, format);
        FDEModel fdem = new FDEModel(Path, format);
        System.out.println(fdem.num_OriTabs+"  "+fdem.num_tabs);

        Model m=new Model();
        BitsetIntVarImpl[] intvar=new BitsetIntVarImpl[fdem.num_vars];
        Tuples[] tuple=new Tuples[fdem.num_tabs];
        for(int i=0;i<fdem.num_vars;i++){
            intvar[i]=new BitsetIntVarImpl(i+"", fdem.vars[i].values, m.ref());
        }
        for(int i=0;i<fdem.num_tabs;i++){
            tuple[i]=new Tuples(fdem.tabs[i].tuples,true);
        }
        for(int i=0;i<fdem.num_OriTabs;i++){
            int[] scp=fdem.tabs[i].scopeInt;
            BitsetIntVarImpl[] scope=new BitsetIntVarImpl[scp.length];
            for(int j=0;j<scp.length;j++){
                scope[j]=intvar[scp[j]];
            }
            Object p=new STRFDEOri(scope,tuple[i]);
//            Object p=new CT(scope,tuple[i]);
//            Object p=new PropTableStr2(scope,tuple[i]);
            Constraint c=new Constraint("TABLE", new Propagator[]{(Propagator)p});
            m.post(c);
        }
        for(int i=fdem.num_OriTabs;i<fdem.num_tabs;i++){
            int[] scp=fdem.tabs[i].scopeInt;
            BitsetIntVarImpl[] scope=new BitsetIntVarImpl[scp.length];
            for(int j=0;j<scp.length;j++){
                scope[j]=intvar[scp[j]];
            }
            Object p=new STRFDEAdd(scope,tuple[i]);
//            Object p=new PropTableStr2(scope,tuple[i]);
//            Object p=new CT(scope,tuple[i]);
            Constraint c=new Constraint("TABLE", new Propagator[]{(Propagator)p});
            m.post(c);
        }

        Solver solver=m.getSolver();
        solver.limitTime(1800000);
        solver.setSearch(new ImpactBased(intvar,false));
        solver.solve();
        System.out.println(solver.getSearch());
        System.out.println(solver.getMeasures());
    }
    public static void solve2(String Path,int format) throws Exception {
        //        XModel xm=new XModel(Path, format);
        FDEModel fdem = new FDEModel(Path, format);
        System.out.println(fdem.num_OriTabs+"  "+fdem.num_tabs);

        Model m=new Model();
        BitsetIntVarImpl[] intvar=new BitsetIntVarImpl[fdem.num_vars];
        Tuples[] tuple=new Tuples[fdem.num_tabs];
        for(int i=0;i<fdem.num_vars;i++){
            intvar[i]=new BitsetIntVarImpl(i+"", fdem.vars[i].values, m.ref());
        }
        for(int i=0;i<fdem.num_tabs;i++){
            tuple[i]=new Tuples(fdem.tabs[i].tuples,true);
        }
        for(int i=0;i<fdem.num_OriTabs;i++){
            int[] scp=fdem.tabs[i].scopeInt;
            BitsetIntVarImpl[] scope=new BitsetIntVarImpl[scp.length];
            for(int j=0;j<scp.length;j++){
                scope[j]=intvar[scp[j]];
            }
            Object p=new STRFDEOri(scope,tuple[i]);
//            Object p=new CT(scope,tuple[i]);
//            Object p=new PropTableStr2(scope,tuple[i]);
            Constraint c=new Constraint("TABLE", new Propagator[]{(Propagator)p});
            m.post(c);
        }
        for(int i=fdem.num_OriTabs;i<fdem.num_tabs;i++){
            int[] scp=fdem.tabs[i].scopeInt;
            BitsetIntVarImpl[] scope=new BitsetIntVarImpl[scp.length];
            for(int j=0;j<scp.length;j++){
                scope[j]=intvar[scp[j]];
            }
            Object p=new STRFDEAdd(scope,tuple[i]);
//            Object p=new PropTableStr2(scope,tuple[i]);
//            Object p=new CT(scope,tuple[i]);
            Constraint c=new Constraint("TABLE", new Propagator[]{(Propagator)p});
            m.post(c);
        }

        Solver solver=m.getSolver();
        solver.limitTime(1800000);
        solver.setSearch(new ImpactBased(intvar,false));
        solver.solve();
        System.out.println(solver.getSearch());
        System.out.println(solver.getMeasures());
    }

}