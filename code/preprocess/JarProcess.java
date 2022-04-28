package ??.??.preprocess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.ConcurrentModificationException;
import java.util.Enumeration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.filefilter.TrueFileFilter;

import ??.??.analysis.PreprocessAnalysis;
import ??.??.configure.Configure;
import ??.??.configure.SootEnvironment;
import ??.??.util.BashRunner;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

public class JarProcess {
	
	public static void extractDexFromJar(String jarDirPath, boolean deleteFlag) {
		// (re)create the directory for saving the extracted Dex files
		File dexDir = new File(Configure.dexOutputDir);
		if (dexDir.exists() && deleteFlag == true) {
			try {
				FileUtils.deleteDirectory(dexDir);
			} catch (IOException ioe) {
				System.err.println(String.format("[Error] cannot delete directory: %s", Configure.dexOutputDir));
				System.exit(0);
			}
		}
		if (!dexDir.exists())
			dexDir.mkdirs();
		
		// traverse system JAR files
		File jarDir = new File(jarDirPath);
		for (File jarFile : FileUtils.listFiles(jarDir, TrueFileFilter.INSTANCE, TrueFileFilter.INSTANCE)) {
			System.out.println(String.format("[Debug] extract -> JAR file: %s", jarFile.getPath())); // Debug
			ZipFile zipFile = null;
			try {
				zipFile = new ZipFile(jarFile);
			} catch (Exception e) {
				System.err.println(String.format("[Error] cannot create ZipFile for: %s", jarFile.getPath()));
				continue;
			}
			
			Enumeration<? extends ZipEntry> zipEntryEnum = zipFile.entries();
			while (zipEntryEnum.hasMoreElements()) {
				ZipEntry zipEntry = zipEntryEnum.nextElement();
				// System.out.println(String.format("[Debug] zip entry: %s", zipEntry.getName())); // Debug
				if (!zipEntry.getName().endsWith(".dex"))
					continue;
				
				// prepare input stream
				InputStream zipEntryIn = null;
				try {
					zipEntryIn = zipFile.getInputStream(zipEntry);
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot get InputStream of ZipEntry %s in ZipFile %s", zipEntry.getName(), jarFile.getPath()));
					continue;
				}
				
				// prepare output stream
				String outputDexPath = Configure.dexOutputDir + File.separator + jarFile.getName().replace(".jar", "") + "-" + zipEntry.getName();
				// System.out.println(String.format("[Debug] output dex path: %s", outputDexPath)); // Debug
				File outputDexFile = new File(outputDexPath);
				if (outputDexFile.exists()) {
					outputDexFile.delete();
				}
				try {
					outputDexFile.createNewFile();
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot create output dex file: %s", outputDexPath));
					continue;
				}
				OutputStream dexOut = null;
				try {
					dexOut = new FileOutputStream(outputDexFile);
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot create OutputStream for output dex file %s", outputDexPath));
					continue;
				}
				
				// flush input stream to output stream
				try {
					int byteRead = 1024;
					while (byteRead > 0) {
						byte[] buffer = new byte[1];
						byteRead = zipEntryIn.read(buffer);
						if (byteRead > 0) {
							dexOut.write(buffer);
							dexOut.flush();
						}
					}
				} catch (Exception e) { }
				
				if (dexOut != null) {
					try {
						dexOut.close();
					} catch (Exception e) { }
				}
			}
			
			if (zipFile != null)
				try {
					zipFile.close();
				} catch (Exception e) { }
		}
	}
	
	public static void extractDexFromApk(String apkDirPath, boolean deleteFlag, String apkLstPath) {
		// (re)create the directory for saving the extracted Dex files
		File dexDir = new File(Configure.dexOutputDir);
		if (dexDir.exists() && deleteFlag == true) {
			try {
				FileUtils.deleteDirectory(dexDir);
			} catch (IOException ioe) {
				System.err.println(String.format("[Error] cannot delete directory: %s", Configure.dexOutputDir));
				System.exit(0);
			}
		}
		if (!dexDir.exists())
			dexDir.mkdirs();
		
		// read paths of APK files need to be analyzed
		ArrayList<String> apkList = new ArrayList<String>();
		if (apkLstPath != null) {
			File apkLst = new File(apkLstPath);
			if (apkLst.exists()) {
				BufferedReader br = null;
				try {
					br = new BufferedReader(new FileReader(apkLst));
					String line = null;
					while((line = br.readLine()) != null) {
						String apkPath = line.split(" ")[1].trim();
						if (apkPath.endsWith(".apk"))
							apkList.add(apkPath);
					}
				} catch (Exception e) { 
					// do nothing
				}
				
				try {
					br.close();
				} catch (Exception e) {
					// do nothing
				}
			}
		}
		
		// traverse system APK files
		File apkDir = new File(apkDirPath);
		for (File apkFile : FileUtils.listFiles(apkDir, TrueFileFilter.INSTANCE, TrueFileFilter.INSTANCE)) {
			if (!apkList.contains(apkFile.getAbsolutePath()))
				continue;
			
			String packageName = BashRunner.getPackageNameofApk(apkFile.getAbsolutePath());
			if (!SootEnvironment.inWhitelist(packageName))
				continue;
			
			System.out.println(String.format("[Debug] extract -> APK file: %s", apkFile.getPath())); // Debug
			ZipFile zipFile = null;
			try {
				zipFile = new ZipFile(apkFile);
			} catch (Exception e) {
				System.err.println(String.format("[Error] cannot create ZipFile for: %s", apkFile.getPath()));
				continue;
			}
			
			Enumeration<? extends ZipEntry> zipEntryEnum = zipFile.entries();
			while (zipEntryEnum.hasMoreElements()) {
				ZipEntry zipEntry = zipEntryEnum.nextElement();
				// System.out.println(String.format("[Debug] zip entry: %s", zipEntry.getName())); // Debug
				if (!zipEntry.getName().endsWith(".dex"))
					continue;
				
				// prepare input stream
				InputStream zipEntryIn = null;
				try {
					zipEntryIn = zipFile.getInputStream(zipEntry);
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot get InputStream of ZipEntry %s in ZipFile %s", zipEntry.getName(), apkFile.getPath()));
					continue;
				}
				
				// prepare output stream
				String outputDexPath = Configure.dexOutputDir + File.separator + apkFile.getName().replace(".apk", "") + "-" + zipEntry.getName();
				// System.out.println(String.format("[Debug] output dex path: %s", outputDexPath)); // Debug
				File outputDexFile = new File(outputDexPath);
				if (outputDexFile.exists()) {
					outputDexFile.delete();
				}
				try {
					outputDexFile.createNewFile();
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot create output dex file: %s", outputDexPath));
					continue;
				}
				OutputStream dexOut = null;
				try {
					dexOut = new FileOutputStream(outputDexFile);
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot create OutputStream for output dex file %s", outputDexPath));
					continue;
				}
				
				// flush input stream to output stream
				try {
					int byteRead = 1024;
					while (byteRead > 0) {
						byte[] buffer = new byte[1];
						byteRead = zipEntryIn.read(buffer);
						if (byteRead > 0) {
							dexOut.write(buffer);
							dexOut.flush();
						}
					}
				} catch (Exception e) { }
				
				if (dexOut != null) {
					try {
						dexOut.close();
					} catch (Exception e) { }
				}
			}
			
			if (zipFile != null) {
				try {
					zipFile.close();
				} catch (Exception e) { }ArrayList<String> commands = new ArrayList<String>();
			}
		}
	}
	
	public static void convertDex2Class(boolean deleteFlag) {
		// (re)create the directory for saving the generate .class files
		File classesDir = new File(Configure.classesOutputDir);
		if (classesDir.exists() && deleteFlag == true) {
			try {
				FileUtils.deleteDirectory(classesDir);
			} catch (IOException ioe) {
				System.err.println(String.format("[Error] cannot delete directory: %s", Configure.classesOutputDir));
				System.exit(0);
			}
		}
		if (!classesDir.exists())
			classesDir.mkdirs();
		
		// traverse each dex file
		File dexDir = new File(Configure.dexOutputDir);
		assert dexDir.isDirectory();
		
		File[] dexFiles = dexDir.listFiles();
		Arrays.sort(dexFiles, Comparator.comparing(File::getName));
		int fileIdx = 1;
		for (File dexFile : dexFiles) {
			System.out.println(String.format("%d/%d: %s", fileIdx++, dexFiles.length, dexFile.getName()));
			// if (!dexFile.getName().startsWith("SamsungTTS-classes"))
				// continue;
			// if (fileIdx <= 144)
				// continue;
			
			// in Preprocess phase, we exclude the cases that cannot be handled by soot, 
			// so that we will not be hindered from these cases in further analysis phases
			System.out.println(String.format("[Debug] convert -> dex file: %s", dexFile.getPath())); // Debug
			SootEnvironment.initForPreprocess(dexFile.getAbsolutePath());
			if (PreprocessAnalysis.needFurtherAnalysis() == true) {
				PackManager.v().writeOutput();
			}
		}
	}
	
	// ---- //
	
	// module-test
	public static void main(String[] args) {
		// extractDexFromJar(Configure.SysDir, true);
		// extractDexFromApk(Configure.AppDir, false, null);
		// extractDexFromApk(Configure.AppDir, false, Configure.AppLst);
		convertDex2Class(false);
	}

}
