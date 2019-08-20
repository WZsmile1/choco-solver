import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

public class TestFDE {
    public static void main(String[] args) throws IOException, SAXException, ParserConfigurationException {
        argEmpty();
    }

    private static void argEmpty() throws ParserConfigurationException, IOException, SAXException {
        File file = new File("D:\\choco-solver\\src\\Experiment\\FDEFolders.xml");
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        DocumentBuilder builder = factory.newDocumentBuilder();
        Document doc = builder.parse(file);
        NodeList inputRoot = doc.getElementsByTagName("inputRoot");
        NodeList outputRoot = doc.getElementsByTagName("outputRoot");
        NodeList inputFolderNodes = doc.getElementsByTagName("folder");

        for (int i = 0; i < inputFolderNodes.getLength(); i++) {
            String folderStr = inputFolderNodes.item(i).getTextContent();
            String inputPath = inputRoot.item(0).getTextContent() + "\\" + folderStr;
            File f = new File(inputPath);
            File[] tempList = f.listFiles();
            File resFile = new File(outputRoot.item(0).getTextContent() + "\\" + folderStr + ".csv");
        }
    }

    private void PointsToCsvFile() {
        // 表格头
        String[] headArr = new String[]{"PointId", "X", "Y"};
        //CSV文件路径及名称
        LocalDateTime localDateTime = LocalDateTime.now();
        DateTimeFormatter df = DateTimeFormatter.ofPattern("yyyyMMddHHmmss");
        String filePath = "E:\\TestCsvDirectory"; //CSV文件路径
        String fileName = "CSV_" + df.format(localDateTime) + ".csv";//CSV文件名称
        File csvFile = null;
        BufferedWriter csvWriter = null;
        try {
            csvFile = new File(filePath + File.separator + fileName);
            File parent = csvFile.getParentFile();
            if (parent != null && !parent.exists()) {
                parent.mkdirs();
            }
            csvFile.createNewFile();

            // GB2312使正确读取分隔符","
            csvWriter = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(csvFile), "GB2312"), 1024);


            // 写入文件头部标题行
            csvWriter.write(String.join(",", headArr));
            csvWriter.newLine();

            // 写入文件内容
            csvWriter.flush();
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            try {
                csvWriter.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

    }
}
