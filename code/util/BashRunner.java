package ??.??.util;

import java.io.IOException;
import java.lang.ProcessBuilder.Redirect;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;

import org.apache.commons.io.IOUtils;

public final class BashRunner {

	private final ArrayList<String> bashCommands;
	private final boolean async;
	private String output;
	
	public BashRunner(ArrayList<String> bashCommands, boolean async){
		this.bashCommands = bashCommands;
		this.async = async;
	}
	
	public String getOutput() {
		return output;
	}
	
	public void run(){
		try {
			ProcessBuilder builder = new ProcessBuilder(this.bashCommands);
			// builder.redirectOutput(Redirect.INHERIT);
			builder.redirectError(Redirect.INHERIT);
			Process process = builder.start();
			output = IOUtils.toString(process.getInputStream(), StandardCharsets.UTF_8);
			
			// wait for thread if not asynchronous
			if(!async) process.waitFor();
		} catch(IOException ioe) {
			ioe.printStackTrace();
		} catch (InterruptedException ie) {
			ie.printStackTrace();
		}
	}
	
	// ---- //
	
	public static String getPackageNameofApk(String apkPath) {
		ArrayList<String> commands = new ArrayList<String>();
		String[] commonCmd = { "/bin/sh", "-c" };
		commands.addAll(Arrays.asList(commonCmd));
		commands.add(String.format("%s %s %s %s", "aapt2", "dump", "packagename", apkPath));
		
		BashRunner bash = new BashRunner(commands, false);
		bash.run();
		String packageName = bash.getOutput().replace("\n", "");
		System.out.println(String.format("[Debug] packageName: %s", packageName));
		return packageName;
	}
	
}