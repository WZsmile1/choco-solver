
import java.io.File

import com.github.tototoshi.csv.CSVWriter
import org.chocosolver.solver.Model
import org.chocosolver.solver.constraints.Propagator
import org.chocosolver.solver.constraints.extension.Tuples
import org.chocosolver.solver.constraints.extension.nary.PropTableStr2
import org.chocosolver.solver.search.strategy.Search.activityBasedSearch
import org.chocosolver.solver.variables.IntVar
import org.chocosolver.solver.variables.impl.BitsetIntVarImpl

import scala.collection.JavaConversions._
import scala.collection.mutable.ArrayBuffer
import scala.util.Sorting
import scala.xml.XML

object testFDE {
  var name = ""
  var pType = ""
  var varType = ""
  var heuName = ""


  def main(args: Array[String]): Unit = {

    if (args.isEmpty)
      argEmpty()
    else
      withArgs(args)
  }

  def argEmpty(): Unit = {
    println(s"hardware cocurrency: ${Runtime.getRuntime.availableProcessors()}")
    val file = XML.loadFile("D:\\choco-solver\\src\\Experiment\\FDEFolders.xml")
    val inputRoot = (file \\ "inputRoot").text
    val outputRoot = (file \\ "outputRoot").text
    val outputFolder = (file \\ "outputFolder").text
    val inputFolderNodes = file \\ "folder"

    for (fn <- inputFolderNodes) {
      val fmt = (fn \\ "@format").text.toInt
      val folderStr = fn.text
      val inputPath = inputRoot + "/" + folderStr
      val files = getFiles(new File(inputPath))
      Sorting.quickSort(files)
      println("exp files:")
      files.foreach(f => println(f.getName))
      val resFile = new File(outputRoot + "/" + outputFolder + folderStr + ".csv")
      val writer = CSVWriter.open(resFile)
      val titleLine = ArrayBuffer[String]()
      titleLine += "name"
      titleLine ++= Array("algorithm", "nodes", "time")
      titleLine ++= Array("algorithm", "nodes", "time")
      titleLine ++= Array("algorithm", "nodes", "time")

      writer.writeRow(titleLine)
      var dataLine = new ArrayBuffer[String](titleLine.length)

      for (f <- files) {
        println("Build Model: " + f.getName)
        val xm = new XModel(f.getPath, true, fmt)
        val fdem = new FDEModel(f.getPath, fmt)
        dataLine.clear()
        dataLine += f.getName()
        //-------------CT串行算法-------------
        val m2 = new org.chocosolver.solver.Model()
        val intvar2 = new Array[BitsetIntVarImpl](xm.num_vars)
        val tuple2 = new Array[Tuples](xm.num_tabs)
        var i = 0
        while (i < xm.num_vars) {
          intvar2(i) = new BitsetIntVarImpl(i + "", xm.vars(i).values, m2.ref)
          i+=1
        }
        i = 0
        while (i < xm.num_tabs) {
          tuple2(i) = new Tuples(xm.tabs(i).tuples, true)
          i+=1
        }
        i = 0
        while (i < xm.num_tabs) {
          val scp = xm.tabs(i).scopeInt
          val scope = new Array[IntVar](scp.length)
          var j = 0
          while (j < scp.length) {
            scope(j) = intvar2(scp(j))
            j+=1
          }
          val p=new PropTableStr2(scope,tuple2(i));
          val pro=Array[Propagator[IntVar]](p);
          val c = new org.chocosolver.solver.constraints.Constraint("TABLE", pro:_*)
          m2.post(c)
          i+=1
        }
        val solver2 = m2.getSolver
        solver2.limitTime(1800000)
//        solver2.setSearch(activityBasedSearch(intvar2:_*))
        solver2.solve
        dataLine += "CT"
        dataLine += solver2.getMeasures.getNodeCount.toString
        dataLine += solver2.getMeasures.getTimeCount.toString


        //-------------CT串行算法-------------
        val m1 = new org.chocosolver.solver.Model()
        val intvar1 = new Array[BitsetIntVarImpl](fdem.num_vars)
        val tuple1 = new Array[Tuples](fdem.num_tabs)
        i = 0
        while (i < fdem.num_vars) {
          intvar1(i) = new BitsetIntVarImpl(i + "", fdem.vars(i).values, m1.ref)
          i+=1
        }
        i = 0
        while (i < fdem.num_tabs) {
          tuple1(i) = new Tuples(fdem.tabs(i).tuples, true)
          i+=1
        }
        i = 0
        while (i < fdem.num_tabs) {
          val scp = fdem.tabs(i).scopeInt
          val scope = new Array[IntVar](scp.length)
          var j = 0
          while (j < scp.length) {
            scope(j) = intvar1(scp(j))
            j+=1
          }
          val p=new PropTableStr2(scope,tuple1(i));
          val pro=Array[Propagator[IntVar]](p);
          val c = new org.chocosolver.solver.constraints.Constraint("TABLE", pro:_*)
          m1.post(c)
          i+=1
        }
        val solver1 = m1.getSolver
        solver1.limitTime(1800000)
//        solver1.setSearch(activityBasedSearch(intvar1:_*))
        solver1.solve
        dataLine += "STR2+FDE"
        dataLine += solver1.getMeasures.getNodeCount.toString
        dataLine += solver1.getMeasures.getTimeCount.toString


        //-------------CT串行算法-------------
        val m = new org.chocosolver.solver.Model()
        val intvar = new Array[BitsetIntVarImpl](fdem.num_vars)
        val tuple = new Array[Tuples](fdem.num_tabs)
        i = 0
        while (i < fdem.num_vars) {
          intvar(i) = new BitsetIntVarImpl(i + "", fdem.vars(i).values, m.ref)
          i+=1
        }
        i = 0
        while (i < fdem.num_tabs) {
          tuple(i) = new Tuples(fdem.tabs(i).tuples, true)
          i+=1
        }
        i = 0
        while (i < fdem.num_OriTabs) {
          val scp = fdem.tabs(i).scopeInt
          val scope = new Array[BitsetIntVarImpl](scp.length)
          var j = 0
          while (j < scp.length) {
            scope(j) = intvar(scp(j))
            j+=1
          }
          val p = new TableFDEOri(scope, tuple(i))
          //            Object p=new CT(scope,tuple[i]);
          //            Object p=new PropTableStr2(scope,tuple[i]);
          val pro=Array[Propagator[BitsetIntVarImpl]](p);
          val c = new org.chocosolver.solver.constraints.Constraint("TABLE", pro:_*)
          m.post(c)
          i+=1
        }
        i = fdem.num_OriTabs
        while (i < fdem.num_tabs) {
          val scp = fdem.tabs(i).scopeInt
          val scope = new Array[BitsetIntVarImpl](scp.length)
          var j = 0
          while (j < scp.length) {
            scope(j) = intvar(scp(j))
            j+=1
          }
          val p = new TableFDEAdd(scope, tuple(i))
          val pro=Array[Propagator[BitsetIntVarImpl]](p);
          val c = new org.chocosolver.solver.constraints.Constraint("TABLE", pro:_*)
          m.post(c)
          i+=1
        }
        val solver = m.getSolver
        solver.limitTime(1800000)
//        solver.setSearch(activityBasedSearch(intvar:_*))
        solver.solve
        dataLine += "FDEbit+FDE"
        dataLine += solver.getMeasures.getNodeCount.toString
        dataLine += solver.getMeasures.getTimeCount.toString

        writer.writeRow(dataLine)
        println("end: " + f.getName)
      }
      writer.close()
      println("-----" + folderStr + " done!-----")
    }
    println("-----All done!-----")
  }

  def withArgs(args: Array[String]): Unit = {

  }

  //获取指定单个目录下所有文件
  def getFiles(dir: File): Array[File] = {
    dir.listFiles.filter(_.isFile) ++
      dir.listFiles.filter(_.isDirectory).flatMap(getFiles)
  }

}
