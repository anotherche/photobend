package bending_crystal_track;

import ij.*;
import ij.process.*;
import net.imagej.updater.CommandLine;
import ij.gui.*;
import ij.io.*;

import java.io.*;
import java.time.Duration;
import java.time.Instant;

import org.bytedeco.javacpp.*;
import org.bytedeco.javacv.Java2DFrameUtils;
import com.drew.imaging.ImageMetadataReader;
import com.drew.metadata.Metadata;
import com.drew.metadata.exif.ExifSubIFDDirectory;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;

import ij.plugin.FolderOpener;
import ij.plugin.filter.*;
import ij.plugin.frame.Recorder;
import ij.measure.ResultsTable;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

import org.bytedeco.opencv.opencv_core.*;
import org.bytedeco.opencv.opencv_core.Point;
import static org.bytedeco.opencv.global.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;
import org.bytedeco.javacpp.indexer.*;

import org.scijava.util.AppUtils;


/* This is an ImageJ plugin providing tracking of 
a needle-like crystal shape changing during photobending process.
Photobending is a phenomenon of crystal deformation caused by non-uniform 
crystal structure transformation due to photochemical reaction. 

Required input is a stack of time lapse images taken during a photobending process.
The output is the time dependence of crystal's curvature and longitude deformation.
The project uses ideas and code of 
1. Template Matching by Qingzong Tseng (based on opencv)
2. javacv (java interface to OpenCV) by Samuel Audet 
3. Exif Metadata Library by Drew Noakes
 */



public class Bending_Crystal_Track implements PlugInFilter, DialogListener {

	
	
	private static final Set<String> videoTypes = new HashSet<String>(java.util.Arrays.asList(
		     new String[] {"WEBM", "MKV", "VOB", "OGV", "OGG", "DRC", "MNG", "AVI", 
		    		 "MOV", "QT", "WMV", "YUV", "RM", "RMVB", "ASF", "AMV", "MP4", 
		    		 "M4P", "MPG", "MP2", "MPEG", "MPE", "MPV", "M2V", 
		    		 "M4V", "SVI", "3GP", "3G2", "MXF", "ROQ", "NSV", "FLV", "F4V", 
		    		 "F4P", "F4A", "F4B" }
		));
	
	private static final String pluginName = "Bending Crystal Track";
	
    ImagePlus imp, ref_Image, refImageBinary, free_ref, free_tpl, holder_ref, mid_ref, mid_tpl;
    ArrayList<ImagePlus> refBinaryFrames;

    GaussianBlur gaussianBlur;
    ImageStack stack;
    Rectangle free_rect, holder_rect, mid_rect;
    Roi free_roi,holder_roi,middle_roi;
    PointRoi proi_free,proi_att,proi_mid;
    int method=5, refSlice, sArea = 20, templSize=300;
    double seconds=0, timeStep=1.0;
    Instant first_shot_time; 
    int width, height, refBitDepth;//, refX_free, refY_free, refX_att, refY_att, refX_mid, refY_mid;
    double refX_free, refY_free, refX_att, refY_att, refX_mid, refY_mid;
    double freeRefCenterShiftX, freeRefCenterShiftY, midRefCenterShiftX, midRefCenterShiftY;
    double disX_free, disY_free, disX_holder, disY_holder, disX_mid, disY_mid, rotAngle, disX_holder_save=0.0, disY_holder_save=0.0;
    double length_ini=0.0, cr_length, hord_ini,
    	   curvature_ini, curvature, 
    	   bending_angle_ini, bending_angle, 
    	   deflection_angle_ini, deflection_angle, 
    	   full_angle, full_angle_ini,
    	   initial_angle,
    	   deformation=0.0;
    double h0_x,h0_y;
    ArrayList<Double> curv_list, deform_list, time_list, freeEnd_matchRes, attEnd_matchRes, mid_matchRes ; 
    double curv_min=0.0, curv_max=0.0, def_min=0.0, def_max = 0.0;
    double free_mideal, att_mideal, mid_mideal;
    
    ImagePlus plotImage, plotDefImage;
    boolean folderMonitoring=true, updateTemplates=false, exifTime=true, saveFlatten=false, videoInput=false, stopPlugin=false,
    		useTimeStamps=true, javacvInstalled = false;
    volatile JDialog stopDlg=null;
    //volatile WaitForUserDialog MonitorDlg=null;
    volatile int stopReason = -1;
    Thread stopThread;
    
    // For movie sequence
    int movieFrameNum=0, previousFrameNum=0;
    double impliedFrameRate;
    ImagePlus prevMovieFrame;
    
    
    
    FloatProcessor result;
    ResultsTable rt, rt_mres;
    String arg;
    int windowSizeX, windowSizeY, iniX, iniY;
    boolean subPixel = true;
    boolean matchIntensity = true;
    boolean showRT = true;
	Roi refCropRoi = null;
	Roi mid_refCropRoi = null;
	double[] matchThreshold=new double[]{0.1, 0.1, 0.05, 0.05, 0.2, 0.2};
	ImageWindow imgWindow;
	Font fontParamInfo;
	
	//boolean doRandomAnalysis=true;
	


	private void setAltTimeMeasure()
	{
		GenericDialog gd = new GenericDialog("Default time step");
        gd.addMessage("The images do not have EXIF data.\n"
        		+ "A constant time step will be used to define creation time of every next image.\n"
        		+ "Change the default time step if necessary.");
        gd.addNumericField("Time step in seconds ", timeStep, 0);
        gd.showDialog();
        timeStep = gd.getNextNumber();
	}
	
	private boolean setStandardCrystalLength() {
		GenericDialog gd = new GenericDialog("Adjust crystal length");
        gd.addMessage("Set standard crystal length to adjust position of the attached end");
        gd.addMessage(String.format("Current crystal length: %.1f", length_ini));
        gd.addNumericField("Standard length in pixels ", length_ini, 0);
        gd.showDialog();
        if (gd.wasCanceled()) {
            return false;
        }
        
        double std_length = gd.getNextNumber();
        refX_att = refX_free + (std_length*(refX_att - refX_free)/length_ini);
        refY_att = refY_free + (std_length*(refY_att - refY_free)/length_ini);
        h0_x=refX_free-refX_att;
        h0_y=refY_free-refY_att;
        length_ini=Math.sqrt(h0_x*h0_x+h0_y*h0_y);
        hord_ini= length_ini;
        
        full_angle_ini=Math.acos(h0_x/hord_ini);
        if (refY_free>refY_att) full_angle_ini=-full_angle_ini;
        
        refX_mid = (refX_free + refX_att)/2;
        refY_mid = (refY_free + refY_att)/2;

        return true;

	}
	
//	private boolean CheckJavaCV(String components) {
//		String javaCVInstallCommand = "Install JavaCV libraries";
//    	Hashtable table = Menus.getCommands();
//		String javaCVInstallClassName = (String)table.get(javaCVInstallCommand);
//		if (javaCVInstallClassName.endsWith("\")")) {
//			int argStart = javaCVInstallClassName.lastIndexOf("(\"");
//			if (argStart>0) {
//				javaCVInstallClassName = javaCVInstallClassName.substring(0, argStart);
//			}
//		}
//		String javaCVInstallNotFound = "JavaCV install plugin is not found. Will try to run without JavaCV installation check.";
//		boolean doRestart = false;
//		if (javaCVInstallClassName!=null) {
//			
//			try {
//				Class c = Class.forName(javaCVInstallClassName);
//				Field restartRequired = c.getField("restartRequired");
//				doRestart = (boolean)restartRequired.get(null);
//				if (doRestart){
//					IJ.showMessage("ImageJ was not restarted after JavaCV installation!");
//					return false;
//				}
//				Method mCheckJavaCV = c.getMethod("CheckJavaCV", String.class, boolean.class, boolean.class);
//				mCheckJavaCV.invoke(null, components, false, false);
//				doRestart = (boolean)restartRequired.get(null);
//				if (doRestart){
//					return false;
//				}
//			} 
//			catch (Exception e) {
//				IJ.log(javaCVInstallNotFound);
//				return true;
//			}
//		}
//		else {
//			IJ.log(javaCVInstallNotFound);
//		}
//		return true;
//	}
	
private boolean checkJavaCV(String version, boolean treatAsMinVer, String components) {
		
		String javaCVInstallCommand = "Install JavaCV libraries";
    	Hashtable table = Menus.getCommands();
		String javaCVInstallClassName = (String)table.get(javaCVInstallCommand);
		if (javaCVInstallClassName==null) {
//			IJ.showMessage("JavaCV check", "JavaCV Installer not found.\n"
//					+"Please install it from from JavaCVInstaller update site:\n"
//					+"https://sites.imagej.net/JavaCVInstaller/");
			
			int result = JOptionPane.showConfirmDialog(null,
					"<html><h2>JavaCV Installer not found.</h2>"
							+ "<br>Please install it from from JavaCVInstaller update site:"
							+ "<br>https://sites.imagej.net/JavaCVInstaller/"
							+ "<br>Do you whant it to be installed now for you?"
							+ "<br><i>you need to restart ImageJ after the install</i></html>",
							"JavaCV check",
                    JOptionPane.YES_NO_OPTION,
                    JOptionPane.QUESTION_MESSAGE);
			if (result == JOptionPane.YES_OPTION) {
				net.imagej.updater.CommandLine updCmd = new net.imagej.updater.CommandLine(AppUtils.getBaseDirectory("ij.dir", CommandLine.class, "updater"), 80);
				updCmd.addOrEditUploadSite("JavaCVInstaller", "https://sites.imagej.net/JavaCVInstaller/", null, null, false);
				net.imagej.updater.CommandLine updCmd2 = new net.imagej.updater.CommandLine(AppUtils.getBaseDirectory("ij.dir", CommandLine.class, "updater"), 80);
				updCmd2.update(Arrays.asList("plugins/JavaCV_Installer/JavaCV_Installer.jar"));
				IJ.run("Refresh Menus");
				table = Menus.getCommands();
				javaCVInstallClassName = (String)table.get(javaCVInstallCommand);
				if (javaCVInstallClassName==null) {
					IJ.showMessage("JavaCV check", "Failed to install JavaCV Installer plugin.\nPlease install it manually.");
				}
			}
			return false;
		}
		
		String installerCommand = "version="
				+ version
				+ " select_installation_option=[Install missing] "
				+ (treatAsMinVer?"treat_selected_version_as_minimal_required ":"")
				+ components;

		boolean saveRecorder = Recorder.record;		//save state of the macro Recorder
		Recorder.record = false;					//disable the macro Recorder to avoid the JavaCV installer plugin being recorded instead of this plugin
		String saveMacroOptions = Macro.getOptions();
		IJ.run("Install JavaCV libraries", installerCommand);
		if (saveMacroOptions != null) Macro.setOptions(saveMacroOptions);
		Recorder.record = saveRecorder;				//restore the state of the macro Recorder
				
		String result = Prefs.get("javacv.install_result", "");
		String launcherResult = Prefs.get("javacv.install_result_launcher", "");
		if (!(result.equalsIgnoreCase("success") && launcherResult.equalsIgnoreCase("success"))) {
			if(result.indexOf("restart")>-1 || launcherResult.indexOf("restart")>-1) {
				IJ.log("Please restart ImageJ to proceed with installation of necessary JavaCV libraries.");
				return false;
			} else {
				IJ.log("JavaCV installation failed. Trying to use JavaCV as is...");
				return true;
			}
		}
		return true;
	}
	
    
	public int setup(String arg, ImagePlus imp) {
    	
		int returnMask = NO_IMAGE_REQUIRED + DOES_8G + DOES_16 +  DOES_32 + DOES_RGB + STACK_REQUIRED;
    	//IJ.run("Install JavaCV libraries", "select=[Install missing] opencv openblas");
    	
		javacvInstalled = checkJavaCV("1.5", true, "opencv");
		if (!javacvInstalled)
    	{
    		stopPlugin=true;
            return returnMask;
    	}
    	
    	
    	GenericDialog pluginMode = new GenericDialog(pluginName);
    	pluginMode.addMessage("Choose from the image source type - video (experimental) or time lapse series");
    	String[] sourceTypes = new String[]{"Time lapse series", "Video file"};
    	pluginMode.addRadioButtonGroup("Source Type", sourceTypes, 2, 1, "Time lapse series");
    	pluginMode.showDialog();
        if (pluginMode.wasCanceled()) {
        	stopPlugin=true;
            return returnMask;
        }
        videoInput = pluginMode.getNextRadioButton().equalsIgnoreCase("Video file");
        int openImpCount = WindowManager.getWindowCount();
        if (videoInput) {
        	
     	
        	ArrayList<String> videoStacks = new ArrayList<String>(0);
    		ArrayList<Integer> videoStackIDs = new ArrayList<Integer>(0);

        	int videoCount=0;
        	for (int srcCnt = 0; srcCnt < openImpCount; srcCnt++) {
        		ImagePlus openImp = WindowManager.getImage(srcCnt+1);
        		if (openImp.getStack()!=null 
        				&& openImp.getStack().getSize()>1 
        				&& openImp.getStack().isVirtual()
        				&& (openImp.getProperty("stack_source_type")!=null &&
        				     openImp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber"))){
        			videoStacks.add(openImp.getTitle());
        			videoStackIDs.add(openImp.getID());
        			videoCount++;

        		}
        		
        	}
        	
        	if (videoCount>0){

            	if (videoCount==1 && WindowManager.getCurrentImage().getID()==videoStackIDs.get(0)){
            		this.imp = WindowManager.getImage(videoStackIDs.get(0));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
            	}
        		GenericDialog gd = new GenericDialog(pluginName);
        		gd.addMessage("Select the video stack or press Cancel to open another video");
        		gd.addChoice("List of open video stacks", videoStacks.toArray(new String[0]), videoStacks.get(0));
        		gd.showDialog();
    			if (!gd.wasCanceled()) {
    				this.imp = WindowManager.getImage(videoStackIDs.get(gd.getNextChoiceIndex()));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
    			}
        	} 


        	
        	String videoReadCommand = "Using FFmpeg...";
        	Hashtable table = Menus.getCommands();
    		String className = (String)table.get(videoReadCommand);
    		if (className==null) {
    			videoReadCommand = "Compressed video";
    			className = (String)table.get(videoReadCommand);
    			if (className==null) {
    				videoReadCommand = "Import Movie Using FFmpeg...";
        			className = (String)table.get(videoReadCommand);
        			if (className==null)
        				IJ.showMessage("FFmpeg_Video plugin is necessary to import compressed video. \nIt can be intalled from the update site http://sites.imagej.net/VideoImportExport.");
    			}
    		}
    		
    		OpenDialog	od = new OpenDialog("Open Video File", "");


    		if (od.getFileName() != null) {
    			//IJ.run("Using FFmpeg...", "open=["+od.getPath()+"] importquiet=true");
    			IJ.run(videoReadCommand, "open=["+od.getPath()+"]");
    			this.imp = WindowManager.getCurrentImage();
    		} else {
    			stopPlugin=true;
    			return returnMask;
    		}
    		
    		
        	//this.imp = WindowManager.getCurrentImage();
        	if (this.imp == null || this.imp.getProperty("stack_source_type")==null ||
        			!this.imp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber")) {
    			stopPlugin=true;
    			return returnMask;
    		}
        	
        } else {
        	ArrayList<String> imgStacks = new ArrayList<String>(0);
    		ArrayList<Integer> imgStackIDs = new ArrayList<Integer>(0);

        	int seqCount=0;
        	for (int srcCnt = 0; srcCnt < openImpCount; srcCnt++) {
        		ImagePlus openImp = WindowManager.getImage(srcCnt+1);
        		

        		if (openImp.getStack()!=null 
        				&& openImp.getStack().getSize()>1 
        				&& openImp.getStack().isVirtual()
        				&& (openImp.getProperty("stack_source_type")==null ||
        				     (openImp.getProperty("stack_source_type")!=null &&
        				     !openImp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber")))){
        			imgStacks.add(openImp.getTitle());
        			imgStackIDs.add(openImp.getID());
        			seqCount++;
        		}
        		
        	}
        	if (seqCount>0){
        		
            	if (seqCount==1 && WindowManager.getCurrentImage().getID()==imgStackIDs.get(0)){
            		this.imp = WindowManager.getImage(imgStackIDs.get(0));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
            	}
        		GenericDialog gd = new GenericDialog(pluginName);
        		gd.addMessage("Select image sequence stack or press Cancel to open another stack");
        		gd.addChoice("List of open virtual stacks", imgStacks.toArray(new String[0]), imgStacks.get(0));
        		gd.showDialog();
    			if (!gd.wasCanceled()) {
    				this.imp = WindowManager.getImage(imgStackIDs.get(gd.getNextChoiceIndex()));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				
    				return returnMask;
    			}
        	} 
        	
        	
        	
        		OpenDialog	od = new OpenDialog("Select first file in the sequence", "");


        		if (od.getFileName() != null) {
        			
        			String sequencePath = od.getPath();
        			String firstFileName = od.getFileName();
        			String extension = "";
        			int i = firstFileName.lastIndexOf('.');
        			if (i > 0 && i < firstFileName.length() - 1) {
        			    extension = firstFileName.substring(i+1);
        			    if (videoTypes.contains(extension.toUpperCase())) {
        			    	IJ.showMessage("Error", "It seems that a video file is selected instead of image file.");
        			    	stopPlugin=true;
                			return returnMask;
        			    }
        			} else {
            			stopPlugin=true;
            			return returnMask;
            		}
        			File[] fileList = (new File(od.getDirectory())).listFiles();
        			ArrayList<String> stackFiles = new ArrayList<String>(0);
	            	int firstFile=0;

	            	for (i = 0; i < fileList.length; i++){
	            		if (fileList[i].isFile() && fileList[i].getName().contains(extension)){
	            			stackFiles.add(fileList[i].getName());
	            		}
	            	}
	            	if (stackFiles.size()<2){
	            		stopPlugin=true;
	        			return returnMask;
	            	} else {
	            		stackFiles.sort(null);//(String::compareToIgnoreCase);
	            		firstFile=stackFiles.indexOf(firstFileName) + 1;
	            	}
	            	if (firstFile==0) {
	        			stopPlugin=true;
	        			return returnMask;
	        		}
	            	
        			IJ.run("Image Sequence...", "open=["+sequencePath+"] starting="+firstFile+" file="+extension+" sort use");
        			this.imp = IJ.getImage();
        			FileInfo fi = new FileInfo();
        			fi.fileName = firstFileName;
        			fi.directory = od.getDirectory();
        			
        			this.imp.setFileInfo(fi);
        			
        		} else {
        			stopPlugin=true;
        			return returnMask;
        		}
        		

        	
        }
        
        return returnMask;
    }
    
    private boolean selectPoints(boolean reselect) {
    	
    	disX_free=0.0;
		disY_free=0.0;
		disX_holder=0.0;
		disY_holder=0.0;
		disX_mid=0.0;
		disY_mid=0.0;
    	
    	Overlay ov;
    	ov = new Overlay();
        imp.setOverlay(ov);
        
        refSlice = imp.getCurrentSlice();
        ref_Image = new ImagePlus(stack.getSliceLabel(refSlice), stack.getProcessor(refSlice));
        
        refImageBinary = ref_Image.duplicate();
        IJ.run(refImageBinary, "Make Binary", "");
        IJ.run(refImageBinary, "Open", "");
        IJ.run(refImageBinary, "Erode", "");
        IJ.run(refImageBinary, "Erode", "");
        IJ.run(refImageBinary, "Find Edges", "");
        IJ.run(refImageBinary, "Invert", "");
        
        refBinaryFrames.add(refImageBinary);
        
        imp.killRoi();
        
        do {
        	IJ.setTool("point");
        	new WaitForUserDialog("Bending_Crystal_Track", "Select a point on the FREE needle's end...\nthen press OK.").show();
        
        	proi_free = (PointRoi)imp.getRoi();
        } while(proi_free==null && 
        		IJ.showMessageWithCancel("Error", "Point is not selected.\nPlease follow the instruction or press cancel to stop."));
        
        if (proi_free==null) return false;
        refX_free=proi_free.getFloatPolygon().xpoints[0];
        refY_free=proi_free.getFloatPolygon().ypoints[0];
        
        
        
        double d1 = refX_free, d2 = width - refX_free, d3 = refY_free, d4 = height - refY_free;
        double dmin = Math.min(Math.min(d1, d2), Math.min(d3, d4));
        if (dmin<=sArea+1)
        {
        	IJ.showMessage("Error", "Search point is to close to the edge.\nReduce template rectangle size on the first dialog.");
            return false;
        }
        
        int rect_half_size=templSize/2;
        double rect_hs_tmp = Math.max(rect_half_size, 0.7*rect_half_size+sArea);
        if (rect_hs_tmp>dmin)
        {
        	rect_half_size =(int) Math.min((dmin-sArea)/0.7, dmin);
        }
        
       
        proi_free.setPointType(3);
        ov.addElement(proi_free);
        imp.setOverlay(ov);
        
        
        imp.killRoi();
        
        
        do {
        	IJ.setTool("point");
        	new WaitForUserDialog("Bending_Crystal_Track", "Select a point on the ATTACHED needle's end...\nthen press OK.").show();
        
        	proi_att = (PointRoi)imp.getRoi();
        } while(proi_att==null && 
        		IJ.showMessageWithCancel("Error", "Point is not selected.\nPlease follow the instruction or press cancel to stop."));
        
        if (proi_att==null) return false;
        refX_att=proi_att.getFloatPolygon().xpoints[0];
        refY_att=proi_att.getFloatPolygon().ypoints[0];
        
        h0_x=refX_free-refX_att;
        h0_y=refY_free-refY_att;
        hord_ini=Math.sqrt(h0_x*h0_x+h0_y*h0_y);
        
        full_angle_ini=Math.acos(h0_x/hord_ini);
        if (refY_free>refY_att) full_angle_ini=-full_angle_ini;
        
        proi_att.setPointType(3);
        ov.addElement(proi_att); 
        Line crystal_line = new Line(refX_free,refY_free,refX_att,refY_att);
        ov.addElement(crystal_line);
        imp.setOverlay(ov);
        
        
        refX_mid = (refX_free + refX_att)/2;
        refY_mid = (refY_free + refY_att)/2;
        
        int dialogButton = JOptionPane.YES_NO_OPTION;
        int dialogResult = JOptionPane.showConfirmDialog(null, "Is the cristal initially straight?", 
        													"Initial crystal bending", dialogButton);
        if(dialogResult == 0) {
          length_ini=hord_ini;
          if (setStandardCrystalLength()) {
        	  proi_att.setLocation(refX_att, refY_att);
        	  ov.addElement(proi_att); 
        	  crystal_line = new Line(refX_free,refY_free,refX_att,refY_att);
              ov.addElement(crystal_line);
              imp.setOverlay(ov);
          }
          
          
        } else {
        	double x0 = refX_mid,
     			   y0 = refY_mid,
     			  
     			   dx = -(refY_free-refY_att),
     			   dy = refX_free-refX_att,
     			   dr = Math.sqrt(dx*dx+dy*dy),
     			   dh = height/2;
             
     				dx/=dr;
     				dy/=dr;
     				
     				
             
             
             
             
             Line mid_line = new Line(x0-dx*dh, y0-dy*dh, x0+dx*dh, y0+dy*dh);
             ov.addElement(mid_line);
             imp.setOverlay(ov);
             
             
             imp.killRoi();
             do {
             	IJ.setTool("point");
             	new WaitForUserDialog("Bending_Crystal_Track", "Select a point in the MIDDLE of the needle...\nthen press OK.").show();
             
             	 proi_mid = (PointRoi)imp.getRoi();
             } while (proi_mid==null && 
             		IJ.showMessageWithCancel("Error", "Point is not selected.\nPlease follow the instruction or press cancel to stop."));
            
             if (proi_mid==null) return false;
             refX_mid=proi_mid.getFloatPolygon().xpoints[0];
             refY_mid=proi_mid.getFloatPolygon().ypoints[0];
             
             
            
             proi_mid.setPointType(3);
             ov.addElement(proi_mid);
             imp.setOverlay(ov);
        } 
        
        
        
        
        
        
        calcBendingParams(reselect);
        
        deflection_angle_ini=deflection_angle;
        bending_angle_ini=bending_angle;
        curvature_ini=curvature;
        initial_angle=full_angle_ini+0.5*bending_angle_ini;
        
        
        
        
        imp.killRoi();
        do {
         	IJ.setTool("rect");
         	new WaitForUserDialog("Bending_Crystal_Track", 
         			"Select a rectangle region around the stationary HOLDER edge.\n"//
            		+"A rectangle around a corner would be the best.\n"//
            		+"Press OK after the selection.").show();
         
         	holder_roi=imp.getRoi();
         } while ((holder_roi==null || !holder_roi.isArea()) && 
         		IJ.showMessageWithCancel("Error", "Region is not selected.\nPlease follow the instruction or press cancel to stop."));
        
         if (holder_roi==null || !holder_roi.isArea()) return false;
            holder_rect = holder_roi.getBounds();
            imp.killRoi();
            holder_roi = new Roi(holder_rect);

        
        ov.addElement(holder_roi);
        imp.setOverlay(ov);
        
        ref_Image.killRoi();
        ref_Image.setRoi(holder_roi);
        holder_ref=ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter holder_ic = new ImageConverter(holder_ref);
        	holder_ic.convertToGray32();
        }
        gaussianBlur = new GaussianBlur();
        
        ImageProcessor ip_tmp=holder_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        
        
        ImagePlus tmp_Ip;
        if (refBitDepth==24 && !matchIntensity) {
				tmp_Ip = holder_ref.duplicate();
				ImageConverter ic = new ImageConverter(tmp_Ip);
        	ic.convertToGray32();
			} else tmp_Ip=holder_ref;
		ImageRoi imageRoi_att = new ImageRoi(holder_rect.x, holder_rect.y,tmp_Ip.getProcessor());
        imageRoi_att.setOpacity(0.3);
        ov.addElement(imageRoi_att);
        imp.setOverlay(ov);
       
       
         
        free_roi=new Roi(refX_free-rect_half_size,refY_free-rect_half_size,2*rect_half_size,2*rect_half_size);
        free_rect = free_roi.getBounds();
        
        
        
        free_roi=new Roi(free_rect);
        
        freeRefCenterShiftX = refX_free - free_rect.x - (free_rect.width - 1)/2.0;
        freeRefCenterShiftY = refY_free - free_rect.y - (free_rect.height - 1)/2.0;
        
        
        ref_Image.killRoi();
        ref_Image.setRoi(free_roi);
        free_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(free_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=free_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);

        free_rect.x+=(int)(free_rect.width*0.15);
        free_rect.y+=(int)(free_rect.height*0.15);
        free_rect.width=(int)(free_rect.width*0.7);
        free_rect.height=(int)(free_rect.height*0.7);
        refCropRoi =  new Roi((int)(free_ref.getWidth()*0.15), (int)(free_ref.getHeight()*0.15), 
				(int)(free_ref.getWidth()*0.7), (int)(free_ref.getHeight()*0.7));
       
        tmp_Ip = free_ref.duplicate();
		tmp_Ip.setRoi(refCropRoi);
		tmp_Ip = tmp_Ip.crop();
        if (refBitDepth==24 && !matchIntensity) {
				
				ImageConverter ic = new ImageConverter(tmp_Ip);
        	ic.convertToGray32();
			} 
		imageRoi_att = new ImageRoi(free_rect.x, free_rect.y,tmp_Ip.getProcessor());
        imageRoi_att.setOpacity(0.3);
        ov.addElement(imageRoi_att);
        imp.setOverlay(ov);
        
        
        d1 = refX_mid;
        d2 = width - refX_mid;
        d3 = refY_mid;
        d4 = height - refY_mid;
        dmin = Math.min(Math.min(d1, d2), Math.min(d3, d4));
        if (dmin<=sArea+1)
        {
        	IJ.showMessage("Error", "Search point is to close to the edge");
            return false;
        }
        
        rect_half_size=templSize/2;
        rect_hs_tmp = Math.max(rect_half_size, 0.7*rect_half_size+sArea);
        if (rect_hs_tmp>dmin)
        {
        	rect_half_size =(int) Math.min((dmin-sArea)/0.7, dmin);
        }
        
        middle_roi=new Roi(refX_mid-rect_half_size,refY_mid-rect_half_size,2*rect_half_size,2*rect_half_size);
        mid_rect = middle_roi.getBounds();
        middle_roi=new Roi(mid_rect);
        
        midRefCenterShiftX = refX_mid -  mid_rect.x - ( mid_rect.width - 1)/2.0 ;
        midRefCenterShiftY = refY_mid -  mid_rect.y - ( mid_rect.height - 1)/2.0;
        
        
        
        ref_Image.killRoi();
        ref_Image.setRoi(middle_roi);
        

        mid_rect.x+=(int)(mid_rect.width*0.15);
        mid_rect.y+=(int)(mid_rect.height*0.15);
        mid_rect.width=(int)(mid_rect.width*0.7);
        mid_rect.height=(int)(mid_rect.height*0.7);
        
        mid_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic_mid = new ImageConverter(mid_ref);
        	ic_mid.convertToGray32();
        }
        
        ip_tmp=mid_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        mid_refCropRoi =  new Roi((int)(mid_ref.getWidth()*0.15), 
        						  (int)(mid_ref.getHeight()*0.15), 
        						  (int)(mid_ref.getWidth()*0.7), 
        						  (int)(mid_ref.getHeight()*0.7));

        
        
        tmp_Ip = mid_ref.duplicate();
		tmp_Ip.setRoi(mid_refCropRoi);
		tmp_Ip = tmp_Ip.crop();
        if (refBitDepth==24 && !matchIntensity) {
				
				ImageConverter ic = new ImageConverter(tmp_Ip);
        	ic.convertToGray32();
			} 
		imageRoi_att = new ImageRoi(mid_rect.x, mid_rect.y,tmp_Ip.getProcessor());
        imageRoi_att.setOpacity(0.3);
        ov.addElement(imageRoi_att);
        imp.setOverlay(ov);
        
        for(ImagePlus refBin : refBinaryFrames) {
        	ImageRoi ref_ImageRoi = new ImageRoi(0, 0,refBin.getProcessor());
	        ref_ImageRoi.setOpacity(0.2);
	        ref_ImageRoi.setZeroTransparent(true);
	        ov.addElement(ref_ImageRoi);
        }
        
        
        imp.setOverlay(ov);
        
        
        if (JOptionPane.showConfirmDialog(null, "Everything is ready.\nPress OK to start.", 
				"Bending_Crystal_Track", JOptionPane.OK_CANCEL_OPTION)==JOptionPane.CANCEL_OPTION) 
        	{
        		
        		imp.killRoi();
        		ov.clear();
        		imp.setOverlay(ov);
        		return false;
        	}
		return true;
    }
    
    private void startControlThread() {
    	stopThread = new Thread(new Runnable()
		{
        	@Override
			public void run() 
			{
//        		WaitForUserDialog dlg = new WaitForUserDialog("Tracking in progress...", "Close this message to stop the track");
//        		dlg.setName("StopThread");
//        		StopDlg=dlg;
//        		dlg.show();
        		stopReason = -1;
    			Object[] options = { "Stop tracking", "Reselect points"}; 
        		JOptionPane optPane = new JOptionPane("Stop the track or reselect measurement points", JOptionPane.INFORMATION_MESSAGE,  JOptionPane.DEFAULT_OPTION,
                        null, options);

        		
        		JDialog dlg = optPane.createDialog("Tracking in progress...");
                
        		
        		
        		//JDialog dlg = new JDialog(null, "Tracking in progress...", Dialog.ModalityType.DOCUMENT_MODAL);
        		//dlg.setContentPane(optPane);
        		dlg.setModalityType(Dialog.ModalityType.DOCUMENT_MODAL);
        		dlg.setName("StopThread");
        		dlg.setDefaultCloseOperation(JDialog.DO_NOTHING_ON_CLOSE);
        		
        		stopDlg=dlg;
        		dlg.pack();
        		dlg.setLocation(10, 10);
        		dlg.setVisible(true);
        		
        		
        		Object selectedValue = optPane.getValue();
        		dlg.dispose();
        		stopDlg = null;

                if(selectedValue == null){
                	stopReason = 0;
                	return;
                }
                
                int maxCounter = options.length;
                for(int counter = 0; counter < maxCounter; counter++) {
                    if(options[counter].equals(selectedValue)) stopReason = counter;
                        return;
                }
                stopReason = 0;
                return;
        		
        		
        		
        		
        		
        		
				
			}
		});
		stopThread.start();	
    }

    
	public void run(ImageProcessor ip) {

		if (stopPlugin) {
			if (javacvInstalled) IJ.showMessage("Error", "No source chosen. Stopping.");
			return;
		}
		
		
		
		fontParamInfo =  new Font("Arial", Font.BOLD, 40);
		imgWindow=imp.getWindow();
		
        stack = imp.getStack();
        
        if (stack.size()<2)  {
        	IJ.showMessage("Error", "There is only 1 slice in the stack.\nNothing to track.");
            return;
        }
        
        if (!videoInput && !stack.isVirtual()) {
        	IJ.showMessage("Error", "Only virtual stacks are supported");
            return;
        }
        
        
        
        if (videoInput){
        	
        	boolean fpsDetected=true;
        	if (imp.getProperty("video_fps")!=null){
        		impliedFrameRate=Double.parseDouble(imp.getProperty("video_fps").toString());//((FFmpeg_FrameReader)stack).getFrameRate();
        	} else {
        		impliedFrameRate=1.0;
        		fpsDetected=false;
        	}
        	GenericDialog gd = new GenericDialog(pluginName);
        	gd.addMessage("Please chose the method of getting the timestamp info\n"
        			+ "\"Frame timestapm\" (default) is useful in case of variable frame rate;\n"
        			+ "\"Calculate from frame rate\" works with constant frame rate video and allows to change the frame rate value.");
        	gd.addRadioButtonGroup("Timestamp source", new String[]{"Frame timestapm", "Calculate from frame rate"}, 2, 1, "Frame timestapm");
        	String fps_detected = String.format("%.3f", impliedFrameRate);
        	if (fpsDetected){
        		gd.addMessage("Frame rate of the video is determined as: "+ fps_detected + " fps.\n"
        			+ "You may redefine the frame rate beneath.");
        	} else {
        		gd.addMessage("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"+
        	"Frame rate of the video cannot be determined. It is arbitrarily set to 1 fps\n"
            			+ "You may redefine the frame rate beneath.\n"+
        				  "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        	}
        	gd.addNumericField("Change frame rate to", impliedFrameRate, 3);

        	gd.showDialog();
        	if (gd.wasCanceled()) {
        		IJ.showMessage("Plugin is canceled.");
        		return;
        	}

        	useTimeStamps=gd.getNextRadioButton().equalsIgnoreCase("Frame timestapm");
        	impliedFrameRate = gd.getNextNumber();
        	if (!useTimeStamps && (impliedFrameRate==Double.NaN || impliedFrameRate<=0)){
        		IJ.showMessage("Wrong frame rate specified. Stopping plugin.");
        		return;
        	}
        }
        
        
		curv_list = new ArrayList<Double>();
        deform_list = new ArrayList<Double>();
        time_list = new ArrayList<Double>();
        
        freeEnd_matchRes = new ArrayList<Double>();
        attEnd_matchRes = new ArrayList<Double>();
        mid_matchRes = new ArrayList<Double>();
        
        
        PlotWindow.noGridLines = false; // draw grid lines
       
        
        
        width = imp.getWidth();
        height = imp.getHeight();
        refBitDepth = imp.getBitDepth();
//        IJ.log("ref bit depth "+refBitDepth);
        refBinaryFrames = new ArrayList<ImagePlus>(0);
		
		
//		Overlay ini_ov = imp.getOverlay();
//		if (ini_ov!=null) {
//			ini_ov.clear();
//			imp.setOverlay(ini_ov);
//		}
		

            if (!getUserParameters()) { return;
            }
            
            if (!selectPoints(false)) return;
            
            

        if (showRT) {
            
        	//rt_mres = new ResultsTable();
        	//rt_mres.show("Matching Results");
        	
        	
        	rt = new ResultsTable();
            
            rt.setDecimalPlaces(2, 2);
			rt.setDecimalPlaces(3, 2);
			rt.setDecimalPlaces(4, 6);
			rt.setDecimalPlaces(5, 6);
			rt.setDecimalPlaces(6, 2);
			rt.setDecimalPlaces(7, 9);
			rt.setDecimalPlaces(8, 6);
			
			rt.show("Results");
            //rt.showRowNumbers(false);

        }
        
        
        FileInfo fi = null;
        String directory = "";
        String name = "";
        
        if(!videoInput){
        	fi = imp.getOriginalFileInfo();
        	directory = fi.directory;
        	name = stack.getSliceLabel(refSlice);
        }
        
    	first_shot_time = getShotTime(directory + name, refSlice);
    	if (first_shot_time==null) exifTime=false;
    	
    	if (saveFlatten) {
    		
    		
			prevMovieFrame = new ImagePlus("",imp.flatten().getProcessor().resize(720));
		}
		
		
		
		
		
		if (showRT) {
            rt.incrementCounter();
            rt.addValue("Time", 0);
            if (videoInput) rt.addValue("File", imp.getTitle() + ":" +stack.getSliceLabel(refSlice).replaceAll(" ", ""));
            else rt.addValue("File", stack.getSliceLabel(refSlice));
            
			rt.addValue("bendAngle", bending_angle_ini);
			rt.addValue("defAngle", deflection_angle_ini);
			rt.addValue("Length", length_ini);
			rt.addValue("Curvature", curvature_ini);
			rt.addValue("Deformation", 0.0);
			
			
			rt.setDecimalPlaces(2, 6);
			rt.setDecimalPlaces(3, 6);
			rt.setDecimalPlaces(4, 2);
			rt.setDecimalPlaces(5, 9);
			rt.setDecimalPlaces(6, 6);
			
            
			rt.show("Results");
            //rt.showRowNumbers(false);
            
            
            
        }

		imp.deleteRoi();
		ref_Image.deleteRoi();
		
		curv_list.add(curvature_ini);
        deform_list.add(0.0);
        time_list.add(0.0);
        
        curv_min=curv_max=curvature_ini;
        
		
                                                    // new plot window
        plotImage = new ImagePlus("Curvature plot", (new Plot("Curvature Plot","Time, s","Curvature")).getProcessor());
        plotImage.show();
        
        plotDefImage = new ImagePlus("Deformation plot", (new Plot("Deformation Plot","Time, s","Deformation")).getProcessor());
        plotDefImage.show();
        
        
//        StopThread = new Thread(new Runnable()
//		{
//        	@Override
//			public void run() 
//			{
////        		WaitForUserDialog dlg = new WaitForUserDialog("Tracking in progress...", "Close this message to stop the track");
////        		dlg.setName("StopThread");
////        		StopDlg=dlg;
////        		dlg.show();
//        		Object[] options = { "Stop tracking", "Reselect points",
//        		        "Stop tracking", "Reselect points" }; 
//        		JOptionPane optPane = new JOptionPane("Stop the track or reselect measurement points", JOptionPane.INFORMATION_MESSAGE,  JOptionPane.DEFAULT_OPTION,
//                        null, Object[] options);
//
//        		JDialog dlg = new JDialog(null, "Tracking in progress...", true);
//        		dlg.setContentPane(optPane);
//        		dlg.setName("StopThread");
//        		StopDlg=dlg;
//        		dlg.setVisible(true);
//        		stopReason = ((Integer)optPane.getValue()).intValue();
//				
//			}
//		});
//		StopThread.start();	
        
        startControlThread();
        
		
        //int i;
        //Random rand = new Random(); 
        //for (int i_slice = refSlice + 1; i_slice < stack.getSize() + 1; i_slice++) {     //align slices after reference slice.
		for (int i = refSlice + 1; i < stack.getSize() + 1; i++) {     //align slices after reference slice.
        	//i=doRandomAnalysis?rand.nextInt(stack.getSize() + 1 - refSlice) + refSlice:i_slice;
        	if (!stopThread.isAlive()) {
        		if (stopReason == 0) {
	        		if (saveFlatten){
	                	
	                	saveFlattenFrames(imp.getOriginalFileInfo().directory + "flatten"+File.separatorChar, 0, true);
	                }
	        		new WaitForUserDialog(pluginName, "The track is finished.").show();
	        		
	        		return;
        		} else {
        			if (!selectPoints(true)) return;
        			startControlThread();
        		}
        	}
//        	Opener opener=null;  
//			String imageFilePath="";
//			ImagePlus imp_new=null;
        	
//			if (!videoInput){
//				opener = new Opener();  
//				imageFilePath = directory+stack.getSliceLabel(i);
//				imp_new = opener.openImage(imageFilePath);
//			}
        	
			Instant startTime = Instant.now();
			ImageProcessor nextIp = imp.getProcessor();
			if (videoInput || (//(new File(imageFilePath)).isFile() &&
					nextIp!=null 
					&& nextIp.getWidth()==width 
					&& nextIp.getHeight()==height 
					&& nextIp.getBitDepth()==refBitDepth)) {
					//&& imp_new!=null 
					//&& imp_new.getWidth()==width 
					//&& imp_new.getHeight()==height 
					//&& imp_new.getBitDepth()==refBitDepth)){

				
					double  tmp_disX_free=disX_free,
							tmp_disY_free=disY_free,
							tmp_disX_holder=disX_holder,
							tmp_disY_holder=disY_holder,
							tmp_disX_mid=disX_mid,
							tmp_disY_mid=disY_mid;
					
					
					imp.setSliceWithoutUpdate(i);
					//int matchresult = analyzeSlice(i, stack.getProcessor(i));
					int matchresult = analyzeSlice(i, nextIp);
					
				    
					if (matchresult==1) {
							disX_free=tmp_disX_free;
							disY_free=tmp_disY_free;
							disX_holder=tmp_disX_holder;
							disY_holder=tmp_disY_holder;
							disX_mid=tmp_disX_mid;
							disY_mid=tmp_disY_mid;
						continue;
					}
					if (matchresult==2) {
						
						if (stopDlg!=null) {
				        	stopDlg.dispose();//.close();
				        	try {
								stopThread.join();
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
				        }
						return;
					}
					if (matchresult==3) {
						selectPoints(true);
					}
		            
		            
		            
		            if (showRT) {
		            	rt.incrementCounter();
		            	
		                rt.addValue("Time", seconds);
		                if (videoInput) rt.addValue("File", imp.getTitle() + ":" +stack.getSliceLabel(i).replaceAll(" ", ""));
		                else rt.addValue("File", stack.getSliceLabel(i));
		                
		                rt.addValue("bendAngle", bending_angle);
						rt.addValue("defAngle", deflection_angle);
						rt.addValue("Length", cr_length);
						rt.addValue("Curvature", curvature);
						rt.addValue("Deformation", deformation);
						
						
						rt.setDecimalPlaces(2, 6);
						rt.setDecimalPlaces(3, 6);
						rt.setDecimalPlaces(4, 2);
						rt.setDecimalPlaces(5, 9);
						rt.setDecimalPlaces(6, 6);
						
		
		                rt.show("Results");
		                //rt.showRowNumbers(false);
		                
		           
		                
		            }
					curv_list.add(curvature);
		            deform_list.add(deformation);
		            time_list.add(seconds);
		            
		            if (curvature>curv_max) curv_max=curvature;
		            if (curvature<curv_min) curv_min=curvature;
		            if (deformation>def_max) def_max=deformation;
		            if (deformation<def_min) def_min=deformation;
		            
					
					  double y_height=curv_max-curv_min; if (y_height==0.0) y_height=1.0; double
					  y_min=curv_min-0.1*y_height, y_max=curv_max+0.1*y_height;
					  
					  Plot plot1 = new Plot("Curvature Plot","Time, s","Curvature");
					  plot1.setLimits(0, seconds, y_min, y_max); plot1.addPoints(time_list,
					  curv_list, Plot.BOX); ImageProcessor plotIp = plot1.getProcessor();
					  plotImage.setProcessor(null, plotIp);
					  
					  y_height=def_max-def_min; if (y_height==0.0) y_height=1.0;
					  y_min=def_min-0.1*y_height; y_max=def_max+0.1*y_height; Plot plot2 = new
					  Plot("Deformation Plot","Time, s","Deformation"); plot2.setLimits(0, seconds,
					  y_min, y_max); plot2.addPoints(time_list, deform_list, Plot.BOX);
					  ImageProcessor plotIp2 = plot2.getProcessor();
					  plotDefImage.setProcessor(null, plotIp2);
					 
        	} else {
        		stack.deleteSlice(i--);
        		imp.setStack(stack);
        	}
			Instant finishTime = Instant.now();
			long timeElapsed = Duration.between(startTime, finishTime).toMillis();
			IJ.showStatus(timeElapsed+" ms");
            
        }
       
        
        
        if (stopDlg!=null) {
        	stopDlg.dispose();//.close();
        	try {
				stopThread.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        }
        	
        
       if (videoInput){
    	   if (saveFlatten){
           	
           	//saveFlattenFrames(((FFmpeg_FrameReader)stack).getDirectory() + "flatten"+File.separatorChar, 0, true);
    		   saveFlattenFrames(imp.getOriginalFileInfo().directory + "flatten"+File.separatorChar, 0, true);
           }
       	return;
       }
        
        GenericDialog gd = new GenericDialog("Monitor for additional images");
        gd.addMessage("Do you want to check/monitor the folder for additional images?");
        gd.showDialog();
        if (gd.wasCanceled()) {
        	if (saveFlatten){
            	
            	saveFlattenFrames(imp.getOriginalFileInfo().directory + "flatten"+File.separatorChar, 0, true);
            }
        	return;
        }
        
        
//        Thread monitorThread = new Thread(new Runnable()
//		{
//        	@Override
//			public void run() 
//			{
//        		WaitForUserDialog dlg = new WaitForUserDialog("Waiting for new images...", "Press OK to stop monitoring the folder");
//				
//				
//        		dlg.setName("MonitorThread");
//        		MonitorDlg=dlg;
//        		dlg.show();
//				
//			}
//		});
//		monitorThread.start();	
        startControlThread();
		
		synchronized (this){
			try {
				this.wait(2000);
				} catch (InterruptedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
		}
			
	        while (true) {
	        	if (!stopThread.isAlive()){
		        	if (stopReason == 0) {
		        		break;
		        		
		        		
	        		} else {
	        			if (!selectPoints(true)) break;
	        			startControlThread();
	        		}
	        	}
	        	
	        	
	        	
	        	
	            	File[] fileList = (new File(directory)).listFiles();
	            	if (fileList != null) {
	            		
		
		            	// Exclude directories
		            	String[] tmplist = new String[fileList.length];
		            	
		            	
		            	int c = 0;
		            	for (int i_file = 0; i_file < fileList.length; i_file++)
		            		if (fileList[i_file].isFile())
		            			tmplist[c++] = fileList[i_file].getName();
		            	if (c>0) {
			            	String[] list = new String[c];
			            	for (int i_file = 0; i_file < c; i_file++) list[i_file] = tmplist[i_file];
			            	
			
			            	// Now exclude non-image files as per the ImageJ FolderOpener
			            	FolderOpener fo = new FolderOpener();
			            	list = fo.trimFileList(list);
			            	if (list != null && list.length>0){
				            	
				            	VirtualStack vstack = (VirtualStack)imp.getStack();
				           
				            	if (list.length > vstack.getSize()) {
				            		String[] imageList = fo.sortFileList(list);
				            		String LastSliceName = vstack.getSliceLabel(imp.getCurrentSlice());//vstack.getSliceLabel(vstack.getSize());
				            		int foundPosition=0;
				            		boolean filefound=false;
				            		for (foundPosition = imageList.length-1; foundPosition>= 0; foundPosition--)
				            		{
				            			if (LastSliceName.equalsIgnoreCase(imageList[foundPosition])){
				            				filefound=true;
				            				break;
				            			}
				            		}
				            		if (filefound)	
				            				for (int j = foundPosition+1; j<imageList.length;j++)
				            				{
				            					
				            					if (!stopThread.isAlive()) break;
				            					
				            					Opener opener = new Opener();  
				            					String imageFilePath = directory+imageList[j];
				            					ImagePlus imp_new = opener.openImage(imageFilePath);
				            					if (imp_new!=null 
				            							&& imp_new.getWidth()==width 
				            							&& imp_new.getHeight()==height 
				            							&& imp_new.getBitDepth()==refBitDepth){
				            						
				            		        		vstack.addSlice(imageList[j]);
					            					
					            					imp.setStack(vstack);
					            					
					            					//imp.setSlice(vstack.getSize());
					            					
					            					
					            					double  tmp_disX_free=disX_free,
					            							tmp_disY_free=disY_free,
					            							tmp_disX_holder=disX_holder,
					            							tmp_disY_holder=disY_holder,
					            							tmp_disX_mid=disX_mid,
					            							tmp_disY_mid=disY_mid;
					            				    	
					            					Instant startTime = Instant.now();
					            					imp.setSliceWithoutUpdate(vstack.getSize());
					            					int matchresult = analyzeSlice(vstack.getSize(),imp_new.getProcessor());
					            					Instant finishTime = Instant.now();
					            					long timeElapsed = Duration.between(startTime, finishTime).toMillis();
					            					IJ.showStatus(timeElapsed+" ms");
					            						
					            						if (matchresult==1) {
					            							disX_free=tmp_disX_free;
					            							disY_free=tmp_disY_free;
					            							disX_holder=tmp_disX_holder;
					            							disY_holder=tmp_disY_holder;
					            							disX_mid=tmp_disX_mid;
					            							disY_mid=tmp_disY_mid;
					            						continue;
					            						}
					            						if (matchresult==2) {
					            							if (stopDlg!=null) {
					            					        	stopDlg.dispose();//.close();
					            					        	try {
					            									stopThread.join();
					            								} catch (InterruptedException e) {
					            									// TODO Auto-generated catch block
					            									e.printStackTrace();
					            								}
					            					        }
					            							return;
					            						}
					            						if (matchresult==3) {
					            							selectPoints(true);
					            						}
						            					
						            		            
						            		            if (showRT) {
						            		            	rt.incrementCounter();
						            		            	rt.addValue("Time", seconds);
						            		            	rt.addValue("File", stack.getSliceLabel(vstack.getSize()));
						            		                
						            		                rt.addValue("bendAngle", bending_angle);
						            						rt.addValue("defAngle", deflection_angle);
						            						rt.addValue("Length", cr_length);
						            						rt.addValue("Curvature", curvature);
						            						rt.addValue("Deformation", deformation);
						            												            											            						
						            						
						            						rt.setDecimalPlaces(2, 6);
						            						rt.setDecimalPlaces(3, 6);
						            						rt.setDecimalPlaces(4, 2);
						            						rt.setDecimalPlaces(5, 9);
						            						rt.setDecimalPlaces(6, 6);
						            						
						            		                
						            		                rt.show("Results");
						            		                //rt.showRowNumbers(false);
						            		                
						            		               
						            		                
						            		            }
						            		            
						            					curv_list.add(curvature);
						            		            deform_list.add(deformation);
						            		            time_list.add(seconds);
						            		            
						            		            if (curvature>curv_max) curv_max=curvature;
						            		            if (curvature<curv_min) curv_min=curvature;
						            		            if (deformation>def_max) def_max=deformation;
						            		            if (deformation<def_min) def_min=deformation;
						            		            
						            		            
						            		            double y_height=curv_max-curv_min;
						            		            if (y_height==0.0) y_height=1.0;
						            		            double y_min=curv_min-0.1*y_height,
						            		            	   y_max=curv_max+0.1*y_height;
						            		            Plot plot1 = new Plot("Curvature Plot","Time, s","Curvature");
						            		            plot1.setLimits(0, seconds, y_min, y_max);
						            		    		plot1.addPoints(time_list, curv_list, Plot.BOX);
						            		    		ImageProcessor plotIp = plot1.getProcessor();
						            		    		plotImage.setProcessor(null, plotIp);
						            		    		
						            		    		y_height=def_max-def_min;
						            		            if (y_height==0.0) y_height=1.0;
						            		            y_min=def_min-0.1*y_height;
						            		            y_max=def_max+0.1*y_height;
						            		             Plot plot2 = new Plot("Deformation Plot","Time, s","Deformation");
						            		             plot2.setLimits(0, seconds, y_min, y_max);
						            		      		plot2.addPoints(time_list, deform_list, Plot.BOX);
						            		     		ImageProcessor plotIp2 = plot2.getProcessor();
						            		     		plotDefImage.setProcessor(null, plotIp2);
				            					}
				            				}
				            			
				            		}
				            		
				            	}
			            	}
		            	}
	            	
	            	
	            	synchronized (this){
		            	try {	
						this.wait(300);
						} catch (InterruptedException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
	            	}
	        }
	        if (saveFlatten){
            	
            	saveFlattenFrames(imp.getOriginalFileInfo().directory + "flatten"+File.separatorChar, 0, true);
            }
        new WaitForUserDialog("Bending Crystal Tracking", "The tracking is finished.").show();
    }
	
	private Instant getShotTime(String imageFilePath, int videoSlice)
	{
		 // the creation time of the image is taken from the EXIF metadata
        
		if (videoInput){
			long timeStampMicroSec = Math.round(Double.parseDouble(stack.getSliceLabel(videoSlice).replaceAll(" s", ""))*1000000);// ((FFmpeg_FrameReader)stack).getFrameTimeStamp(videoSlice - 1);
			if (useTimeStamps) return Instant.ofEpochSecond(0L, timeStampMicroSec*1000L);
			else return Instant.ofEpochSecond(0L, Math.round(1000000000.0*(videoSlice - 1)/impliedFrameRate));
		}
	       
		File jpegFile = new File(imageFilePath);
		
		Metadata metadata;
		
		try {
			metadata = ImageMetadataReader.readMetadata(jpegFile);
			ExifSubIFDDirectory md_directory = metadata.getFirstDirectoryOfType(ExifSubIFDDirectory.class);
		    return md_directory.getDateOriginal().toInstant();//new DateTime(md_directory.getDateOriginal());
			
		} catch (Exception e) {
			setAltTimeMeasure();
			return null;
		}
				
	}
	
	/*
	private boolean testMatchResult(double result, double ref, int method) {
	
		boolean successfulMatch = true;
		double thrsh=matchThreshold[method];
		switch (method) {
    	case 0:
    		if (result/ref>thrsh) successfulMatch = false;
    		break;
    	case 1:
    		if (result>thrsh) successfulMatch = false;
    		break;
    	case 2:
    		if (Math.abs((result-ref)/ref)>thrsh) successfulMatch = false;
    		break;
    	case 3:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
    	case 4:
    		if (Math.abs(result-ref)/ref>thrsh) successfulMatch = false;
    		break;
    	case 5:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
		}
		return successfulMatch;
    
	}
*/
	
	private boolean testMatchResult(double result, double ref, int method, double x, double y, int searchWidth, int tplSize) {
		
		boolean successfulMatch = true;
		double distTrsh=Math.min(0.05*tplSize, 0.05*searchWidth);
		double thrsh=matchThreshold[method];
		switch (method) {
    	case 0:
    		if (result/ref>thrsh) successfulMatch = false;
    		break;
    	case 1:
    		if (result>thrsh) successfulMatch = false;
    		break;
    	case 2:
    		if (Math.abs((result-ref)/ref)>thrsh) successfulMatch = false;
    		break;
    	case 3:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
    	case 4:
    		if (Math.abs(result-ref)/ref>thrsh) successfulMatch = false;
    		break;
    	case 5:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
		}
		if (searchWidth!=0 &&  ((x<distTrsh) || (y<distTrsh) || (x>searchWidth-distTrsh) || (y>searchWidth-distTrsh))) successfulMatch = false;
		
		
		return successfulMatch;
    
	}
	
	private void adjustThreshold(double result, double ref, int method) {
		
		
		switch (method) {
    	case 0:
    		matchThreshold[method] =1.1*result/ref;
    		break;
    	case 1:
    		matchThreshold[method] =1.1*result;
    		break;
    	case 2:
    	case 4:
    		matchThreshold[method] =1.1*Math.abs((result-ref)/ref);
    		break;
    	case 3:
    	case 5:	
    		matchThreshold[method] =1.1*Math.abs(result-ref);
    		break;
    	
		}
		
    
	}
	
	private int failureQuestionDlg(int place) {
		Object[] options1 = { "Keep the result", "Skip the frame",
        "Stop tracking", "Reselect points" };
		String placeName = (place==0?"holder":(place==1?"free end":"middle part"));  
		JPanel panel = new JPanel();
		panel.add(new JLabel("<html>Match of the "+placeName+" is poor."
				+ "<br>Select one of the possibilities:"
				+ "<br>1. Accept the match and continue"
				+ "<br>2. Skip this frame and continue"
				+ "<br>3. Stop the tracking"
				+ "<br>4. Reselect points</html>"));
		

		imgWindow.toFront();
		int result = JOptionPane.showOptionDialog(null, panel, "Match is poor",
        JOptionPane.DEFAULT_OPTION, JOptionPane.QUESTION_MESSAGE,
        null, options1, null);
		if (result== JOptionPane.CLOSED_OPTION) return 1;
		//if (result== JOptionPane.NO_OPTION) return 1;
		//return 2;
		return result;
	}

    private int analyzeSlice(int slice, ImageProcessor slice_proc) {

 
//    	long timeElapsed0=0, timeElapsed1=0, timeElapsed2=0, timeElapsed3=0, timeElapsed4=0, timeElapsed5=0, timeElapsed6=0;
//    	Instant CPUTime6 = Instant.now();
        double[] coord_res = new double[3]; 
        Overlay overlay;
        
        ImagePlus free_tar = new ImagePlus("",slice_proc);
        ImagePlus holder_tar= new ImagePlus("",slice_proc);
        ImagePlus mid_tar = new ImagePlus("",slice_proc);
        ImagePlus tmpIp;
        
         int xStart_free=0 ,yStart_free=0, sWX_free=width, sWY_free=height, 
        	 xStart_holder=0, yStart_holder=0, sWX_holder=width, sWY_holder=height,
        	 xStart_mid=0 ,yStart_mid=0, sWX_mid=width, sWY_mid=height;
        
        double dxtmp=0.0, dytmp=0.0;

        if (sArea != 0) {


        	// Specifying coordinates of the search rectangle around the free end
        	
            xStart_free = free_rect.x + (int)disX_free - sArea;
            yStart_free = free_rect.y + (int)disY_free - sArea;
            sWX_free = free_rect.width + 2 * sArea;
            sWY_free = free_rect.height + 2 * sArea;

            if (xStart_free < 0) {
                xStart_free = 0;
            }
            if (yStart_free < 0) {
                yStart_free = 0;
            }
            if (xStart_free + sWX_free > width) {
                xStart_free = width - sWX_free;
            }
            if (yStart_free + sWY_free > height) {
                yStart_free = height - sWY_free;
            }
            
            // Small image containing free crystal's end
            free_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
            free_tar=free_tar.crop();
            
           
            
            // Specifying coordinates of the search rectangle around the holder part
            
            xStart_holder = holder_rect.x + (int)disX_holder - sArea;
            yStart_holder = holder_rect.y + (int)disY_holder - sArea;
            
            sWX_holder = holder_rect.width + 2 * sArea;
            sWY_holder = holder_rect.height + 2 * sArea;

            if (xStart_holder < 0) {
                xStart_holder = 0;
            }
            if (yStart_holder < 0) {
                yStart_holder = 0;
            }
            if (xStart_holder + sWX_holder > width) {
                xStart_holder = width - sWX_holder;
            }
            if (yStart_holder + sWY_holder > height) {
                yStart_holder = height - sWY_holder;
            }
            
            // Small image containing needed holder part
            holder_tar.setRoi(xStart_holder, yStart_holder, sWX_holder, sWY_holder);
            holder_tar=holder_tar.crop();
            
            
// Specifying coordinates of the search rectangle around the middle part
            
            double x0 = (refX_free+disX_free+refX_att+disX_holder)/2.0,
     			   y0 = (refY_free+disY_free+refY_att+disY_holder)/2.0,
     			   
     			   x1,y1,
     			   dx = -(refY_free+disY_free-(refY_att+disY_holder)),
     			   dy = refX_free+disX_free-(refX_att+disX_holder),
     			   dr = Math.sqrt(dx*dx+dy*dy),
     			   dh=0.0;
            if (curvature!=0.0)
            	dh = (1-Math.cos(curvature*cr_length/2.0))/curvature;
             
     				dx/=dr;
     				dy/=dr;
     				
     				x1 = x0 + dx*dh;
     				y1 = y0 + dy*dh;
            
           
            
     		xStart_mid = (int)(x1 - (mid_rect.width)/2.0 - sArea);
     	    yStart_mid = (int)(y1 - (mid_rect.height)/2.0 - sArea);
            
            
 			
            sWX_mid = mid_rect.width + 2 * sArea;
            sWY_mid = mid_rect.height + 2 * sArea;

            if (xStart_mid < 0) {
                xStart_mid = 0;
            }
            if (yStart_mid < 0) {
                yStart_mid = 0;
            }
            if (xStart_mid + sWX_mid > width) {
                xStart_mid = width - sWX_mid;
            }
            if (yStart_mid + sWY_mid > height) {
                yStart_mid = height - sWY_mid;
            }
            
            // Small image containing central crystal's part
            mid_tar.setRoi(xStart_mid, yStart_mid, sWX_mid, sWY_mid);
            mid_tar=mid_tar.crop();
            
            
 
        } else {
        	// Needed parts will be searched over the whole slice
          
        }
        
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(free_tar);
        	ic.convertToGray32();
        	ImageConverter holder_ic = new ImageConverter(holder_tar);
        	holder_ic.convertToGray32();
        	ImageConverter mid_ic = new ImageConverter(mid_tar);
        	mid_ic.convertToGray32();
        }
        gaussianBlur.blurGaussian(free_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(holder_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(mid_tar.getProcessor(), 2, 2, 0.02);
        
        //int idealMethod=(method==0?2:method);
        att_mideal= doMatch_test(holder_ref.getProcessor(),(method==0?2:method));
        coord_res = doMatch_coord_res(holder_tar.getProcessor(), holder_ref.getProcessor(), method, subPixel, null);
        
        boolean ignoreFrame=false, stopTracking=false, reselectPoints=false;
        if (!testMatchResult(coord_res[2], att_mideal, method, coord_res[0], coord_res[1], sArea*2, Math.min(holder_rect.width, holder_rect.height))) { ///////// The holder is not found...
        	if (sArea!=0) {										  ///////// Let's try global search if it was local search before
        		
        		/*
        		overlay = new Overlay();
        		if (refBitDepth==24 && !matchIntensity) {
     				tmpIp = holder_ref.duplicate();
     				ImageConverter ic = new ImageConverter(tmpIp);
                	ic.convertToGray32();
     			} else tmpIp=holder_ref;
    			ImageRoi imageRoi_att1 = new ImageRoi((int)coord_res[0]+xStart_holder, (int)coord_res[1]+yStart_holder,tmpIp.getProcessor());
    	        imageRoi_att1.setOpacity(0.3);
    	        overlay.addElement(imageRoi_att1);
    			imp.setSlice(slice);
    			imp.setOverlay(overlay);
    			*/
        		
        		xStart_holder=yStart_holder=0;        		
        		ImagePlus full_tar= new ImagePlus("",slice_proc);
        		if (matchIntensity) {
        			ImageConverter ic = new ImageConverter(full_tar);
        			ic.convertToGray32();
        			
        		}
        		gaussianBlur.blurGaussian(full_tar.getProcessor(), 2, 2, 0.02);
        		coord_res = doMatch_coord_res(full_tar.getProcessor(), holder_ref.getProcessor(), method, subPixel, null);
        		if (!testMatchResult(coord_res[2], att_mideal, method, coord_res[0], coord_res[1], 0, Math.min(holder_rect.width, holder_rect.height))) { ////////////// Not found globally
        			overlay = new Overlay();
        			if (refBitDepth==24 && !matchIntensity) {
         				tmpIp = holder_ref.duplicate();
         				ImageConverter ic = new ImageConverter(tmpIp);
                    	ic.convertToGray32();
         			} else tmpIp=holder_ref;
        			ImageRoi imageRoi_att = new ImageRoi((int)coord_res[0], (int)coord_res[1],tmpIp.getProcessor());
        	        imageRoi_att.setOpacity(0.3);
        	        overlay.addElement(imageRoi_att);
        			imp.setSlice(slice);
        			imp.setOverlay(overlay);
        			int failureAnswer = failureQuestionDlg(0); 
        			if (failureAnswer==0) adjustThreshold(coord_res[2], att_mideal, method);
        			ignoreFrame = (failureAnswer==1);
        			stopTracking = (failureAnswer==2);
        			reselectPoints = (failureAnswer==3);
        		} else {												///////////// The holder was found shifted. Shift search areas and continue
        			
        			        free_tar = new ImagePlus("",slice_proc);
        	               	mid_tar = new ImagePlus("",slice_proc);
        					double xShift = coord_res[0] - holder_rect.x - disX_holder,
        							yShift = coord_res[1] - holder_rect.y - disY_holder;

        					xStart_free += xShift;
        		            yStart_free += yShift;
        		            

        		            if (xStart_free < 0) {
        		                xStart_free = 0;
        		            }
        		            if (yStart_free < 0) {
        		                yStart_free = 0;
        		            }
        		            if (xStart_free + sWX_free > width) {
        		                xStart_free = width - sWX_free;
        		            }
        		            if (yStart_free + sWY_free > height) {
        		                yStart_free = height - sWY_free;
        		            }
        		            
        		            // Small image containing free crystal's end
        		            free_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
        		            free_tar=free_tar.crop();
        		            
        		            xStart_mid += xShift;
        		     	    yStart_mid += yShift;
        		            
        		            if (xStart_mid < 0) {
        		                xStart_mid = 0;
        		            }
        		            if (yStart_mid < 0) {
        		                yStart_mid = 0;
        		            }
        		            if (xStart_mid + sWX_mid > width) {
        		                xStart_mid = width - sWX_mid;
        		            }
        		            if (yStart_mid + sWY_mid > height) {
        		                yStart_mid = height - sWY_mid;
        		            }
        		            
        		            // Small image containing central crystal's part
        		            mid_tar.setRoi(xStart_mid, yStart_mid, sWX_mid, sWY_mid);
        		            mid_tar=mid_tar.crop();
        		            
        		            if (matchIntensity) {
        		            	ImageConverter ic = new ImageConverter(free_tar);
        		            	ic.convertToGray32();
        		            	ImageConverter mid_ic = new ImageConverter(mid_tar);
        		            	mid_ic.convertToGray32();
        		            }
        		            gaussianBlur.blurGaussian(free_tar.getProcessor(), 2, 2, 0.02);        
        		            gaussianBlur.blurGaussian(mid_tar.getProcessor(), 2, 2, 0.02);
        		            
       		            
        		}
        	} else { ///////////////// The search was initially global but the holder was not found 
        		overlay = new Overlay();
        		if (refBitDepth==24 && !matchIntensity) {
     				tmpIp = holder_ref.duplicate();
     				ImageConverter ic = new ImageConverter(tmpIp);
                	ic.convertToGray32();
     			} else tmpIp=holder_ref;
    			ImageRoi imageRoi_att = new ImageRoi((int)coord_res[0], (int)coord_res[1],tmpIp.getProcessor());
    	        imageRoi_att.setOpacity(0.3);
    	        overlay.addElement(imageRoi_att);
    			imp.setSlice(slice);
    			imp.setOverlay(overlay);
        		int failureAnswer = failureQuestionDlg(0); 
        		if (failureAnswer==0) adjustThreshold(coord_res[2], att_mideal, method);
    			ignoreFrame = (failureAnswer==1);
    			stopTracking = (failureAnswer==2);
    			reselectPoints = (failureAnswer==3);
        	}
        }
        
        if (ignoreFrame) return 1;
        if (stopTracking) return 2;
        if (reselectPoints) return 3;
        
        attEnd_matchRes.add(coord_res[2]);
        
        disX_holder = coord_res[0] + xStart_holder - holder_rect.x;
        disY_holder = coord_res[1] + yStart_holder - holder_rect.y;
        
        //// not working part of the template update code
        
        //if (updateTemplates)
        //{
        //	holder_ref = new ImagePlus("",tmptar);
        //	holder_ref.setRoi(new Roi(holder_rect.x + disX_holder, holder_rect.y + disY_holder, (double)holder_rect.width, (double)holder_rect.height));
        //    holder_ref=holder_ref.crop();
        //    ImageConverter holder_ic = new ImageConverter(holder_ref);
        //    holder_ic.convertToGray8();
        //    gaussianBlur = new GaussianBlur();
        //    ImageProcessor ip_tmp=holder_ref.getProcessor();
        //    gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        	
        //}
        
        // The block of the free end search
        // We make iterations to find position of the rotated template 
        // of the free crystal's end
        // Iterations finish upon the convergence (but not more than 10 iterations are taken)
        
        for (int iter=0;iter<10;iter++)
        {
        	
        	// rotation angle is computed from the previous value of the bending angle  
        	
        	double angle = - (full_angle + 0.5*bending_angle - initial_angle)*180/Math.PI;
    		
    		
    			// A copy of the template is rotated..
    			free_tpl = free_ref.duplicate();
      			ImageProcessor tpl_ip = free_tpl.getProcessor();
    			tpl_ip.setInterpolationMethod(ImageProcessor.BICUBIC);
    			tpl_ip.rotate(angle);
    			free_tpl.setRoi(refCropRoi);
    			free_tpl=free_tpl.crop();
    			
    			
    			// ... and fitted
    			free_mideal=doMatch_test(free_tpl.getProcessor(), (method==0?2:method));
    			coord_res = doMatch_coord_res(free_tar.getProcessor(), free_tpl.getProcessor(), method, subPixel, null);
    			if (!testMatchResult(coord_res[2], free_mideal, method, coord_res[0], coord_res[1], sArea*2, Math.min(free_rect.width, free_rect.height))) {
    				
    				
    				int sArea_new=sArea;
    				boolean newfreePositionFound=false, leftBound=false, rightBound=false, bottomBound=false, upperBound=false;
    				while(!newfreePositionFound && !(leftBound && rightBound && bottomBound && upperBound)){
    				
    					
    					sArea_new*=2;
    					//IJ.showMessage("Try to find in area = " + sArea_new);
    					xStart_free = free_rect.x + (int)disX_free - sArea_new;
    		            yStart_free = free_rect.y + (int)disY_free - sArea_new;
    		            sWX_free = free_rect.width + 2 * sArea_new;
    		            sWY_free = free_rect.height + 2 * sArea_new;

    		            if (xStart_free < 0) {
    		                xStart_free = 0;
    		                leftBound=true;
    		            }
    		            if (yStart_free < 0) {
    		                yStart_free = 0;
    		                upperBound=true;
    		            }
    		            if (xStart_free + sWX_free > width) {
    		                xStart_free = width - sWX_free;
    		                rightBound=true;
    		            }
    		            if (yStart_free + sWY_free > height) {
    		                yStart_free = height - sWY_free;
    		                bottomBound=true;
    		            }
    		            
    		            free_tar = new ImagePlus("",slice_proc);
    		            // Small image containing free crystal's end
    		            free_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
    		            free_tar=free_tar.crop();
    		            
    		            if (matchIntensity) {
    		            	ImageConverter ic = new ImageConverter(free_tar);
    		            	ic.convertToGray32();
    		            	
    		            }
    		            gaussianBlur.blurGaussian(free_tar.getProcessor(), 2, 2, 0.02);        
    		            
    		            coord_res = doMatch_coord_res(free_tar.getProcessor(), free_tpl.getProcessor(), method, subPixel, null);
    		            
    	    			if (!testMatchResult(coord_res[2], free_mideal, method, coord_res[0], coord_res[1], sArea_new*2, Math.min(free_rect.width, free_rect.height))) {
    	    				
    	    				
    	    				if (refBitDepth==24 && !matchIntensity) {
    	         				tmpIp = free_tpl.duplicate();
    	         				ImageConverter ic = new ImageConverter(tmpIp);
    	                    	ic.convertToGray32();
    	         			} else tmpIp=free_tpl;
    	        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_free, (int)coord_res[1]+ yStart_free,tmpIp.getProcessor());
    	        	        imageRoi.setOpacity(0.3);
    	        	        overlay = new Overlay();
    	        	        overlay.addElement(imageRoi);
    	        			//imp.setSlice(slice);
    	        	        //WaitForUserDialog dlg = new WaitForUserDialog("Not found", "angle = "+angle+"\nfull_angle = "+full_angle+"\nbending_angle = "+bending_angle+"\ninitial_angle = "+initial_angle+"\nideal res = "+free_mideal);
    	        	        //dlg.show();
    	        			overlay.addElement(new Roi(xStart_free, yStart_free, sWX_free, sWY_free));
    	        			imp.setSlice(slice);
    	        			imp.setOverlay(overlay);
    	        			//IJ.showMessage("Not found in Area=" + sArea_new);
    	    				
    	    			} else {
    	    				//IJ.showMessage("Found in Area = " + sArea_new);
    	    				newfreePositionFound=true;
    	    			}
    		            
    				}
    				
    				
    				
    				
    				
    				if (!newfreePositionFound){
	    				overlay = new Overlay();
	    				if (refBitDepth==24 && !matchIntensity) {
	         				tmpIp = free_tpl.duplicate();
	         				ImageConverter ic = new ImageConverter(tmpIp);
	                    	ic.convertToGray32();
	         			} else tmpIp=free_tpl;
	        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_free, (int)coord_res[1]+ yStart_free,tmpIp.getProcessor());
	        	        imageRoi.setOpacity(0.3);
	        	        overlay.addElement(imageRoi);
	        			imp.setSlice(slice);
	        			imp.setOverlay(overlay);
	        			
	    				int failureAnswer = failureQuestionDlg(1); 
	    				if (failureAnswer==0) adjustThreshold(coord_res[2], free_mideal, method);
	        			ignoreFrame = (failureAnswer==1);
	        			stopTracking = (failureAnswer==2);
	        			reselectPoints = (failureAnswer==3);
    				}
        		}
    			
    			if (ignoreFrame) return 1;
    	        if (stopTracking) return 2;
    	        if (reselectPoints) return 3;
 
    	        if (iter>0) freeEnd_matchRes.remove(freeEnd_matchRes.size()-1);
    			freeEnd_matchRes.add(coord_res[2]);
    			
    			disX_free = coord_res[0] + xStart_free - free_rect.x;
                disY_free = coord_res[1] + yStart_free - free_rect.y;
                if (subPixel) {
                	
                	disX_free += freeRefCenterShiftX*(Math.cos(angle*Math.PI/180.0) - 1.0) + freeRefCenterShiftY*Math.sin(angle*Math.PI/180.0);
                	disY_free += freeRefCenterShiftY*(Math.cos(angle*Math.PI/180.0) - 1.0) - freeRefCenterShiftX*Math.sin(angle*Math.PI/180.0);
                }

            
            
            mid_tpl = mid_ref.duplicate();
			
			ImageProcessor mid_ip = mid_tpl.getProcessor();
			mid_ip.setInterpolationMethod(ImageProcessor.BICUBIC);
		
			double H_x=refX_free+disX_free-(refX_att+disX_holder),
		          	   H_y=refY_free+disY_free-(refY_att+disY_holder),
		          	   H=Math.sqrt(H_x*H_x+H_y*H_y),
		          	   cos_full_angle=(H_x)/H,
		          	   mid_angle = (Math.signum(-H_y)*Math.acos(cos_full_angle) - full_angle_ini)*180/Math.PI;
			
			mid_ip.rotate(-mid_angle);
			mid_tpl.setRoi(mid_refCropRoi);
			mid_tpl=mid_tpl.crop();
			mid_mideal=doMatch_test(mid_tpl.getProcessor(),(method==0?2:method));
			


			double x0 = (refX_free+disX_free+refX_att+disX_holder)/2.0 - (mid_rect.width)/2.0 - xStart_mid,
				   y0 = (refY_free+disY_free+refY_att+disY_holder)/2.0 - (mid_rect.height)/2.0 - yStart_mid,
				   dx = -(refY_free+disY_free-(refY_att+disY_holder)),
				   dy = refX_free+disX_free-(refX_att+disX_holder),
				   dr = Math.sqrt(dx*dx+dy*dy);
			
			
			double dh=0.0;
            if (curvature!=0.0)
            	dh = (1-Math.cos(curvature*cr_length/2.0))/curvature;
             
     				dx/=dr;
     				dy/=dr;
     				
     				x0 += dx*dh;
     				y0 += dy*dh;
			
     		double[] lineCoord = new double[4];
     		lineCoord[0]=x0;
     		lineCoord[1]=y0;
     		lineCoord[2]=dx;
     		lineCoord[3]=dy;
     		coord_res = doMatch_coord_res(mid_tar.getProcessor(), mid_tpl.getProcessor(), method, subPixel, lineCoord);
     		
     		if (!testMatchResult(coord_res[2], mid_mideal, method, coord_res[0], coord_res[1], sArea*2, Math.min(mid_rect.width, mid_rect.height))) {
     			
     			
     			
     			int sArea_new=sArea;
				boolean newmidPositionFound=false, leftBound=false, rightBound=false, bottomBound=false, upperBound=false;
				while(!newmidPositionFound && !(leftBound && rightBound && bottomBound && upperBound)){
				
					
					sArea_new*=2;
					//IJ.showMessage("Try to find in area = " + sArea_new);
					xStart_mid = mid_rect.x + (int)disX_mid - sArea_new;
		            yStart_mid = mid_rect.y + (int)disY_mid - sArea_new;
		            sWX_mid = mid_rect.width + 2 * sArea_new;
		            sWY_mid = mid_rect.height + 2 * sArea_new;

		            if (xStart_mid < 0) {
		                xStart_mid = 0;
		                leftBound=true;
		            }
		            if (yStart_mid < 0) {
		                yStart_mid = 0;
		                upperBound=true;
		            }
		            if (xStart_mid + sWX_mid > width) {
		                xStart_mid = width - sWX_mid;
		                rightBound=true;
		            }
		            if (yStart_mid + sWY_mid > height) {
		                yStart_mid = height - sWY_mid;
		                bottomBound=true;
		            }
		            
		            
		             x0 = (refX_free+disX_free+refX_att+disX_holder)/2.0 - (mid_rect.width)/2.0 - xStart_mid;
		 				   y0 = (refY_free+disY_free+refY_att+disY_holder)/2.0 - (mid_rect.height)/2.0 - yStart_mid;
		 				   dx = -(refY_free+disY_free-(refY_att+disY_holder));
		 				   dy = refX_free+disX_free-(refX_att+disX_holder);
		 				   dr = Math.sqrt(dx*dx+dy*dy);
		 			
		 			
		 			 dh=0.0;
		             if (curvature!=0.0)
		             	dh = (1-Math.cos(curvature*cr_length/2.0))/curvature;
		              
		      				dx/=dr;
		      				dy/=dr;
		      				
		      				x0 += dx*dh;
		      				y0 += dy*dh;
		 			
		      		//double[] lineCoord = new double[4];
		      		lineCoord[0]=x0;
		      		lineCoord[1]=y0;
		      		lineCoord[2]=dx;
		      		lineCoord[3]=dy;
		            
		            
		            mid_tar = new ImagePlus("",slice_proc);
		            // Small image containing free crystal's end
		            mid_tar.setRoi(xStart_mid, yStart_mid, sWX_mid, sWY_mid);
		            mid_tar=mid_tar.crop();
		            
		            if (matchIntensity) {
		            	
		            	ImageConverter mid_ic = new ImageConverter(mid_tar);
		            	mid_ic.convertToGray32();
		            }
		                  
		            gaussianBlur.blurGaussian(mid_tar.getProcessor(), 2, 2, 0.02);
		            coord_res = doMatch_coord_res(mid_tar.getProcessor(), mid_tpl.getProcessor(), method, subPixel, lineCoord);
		            
	    			if (!testMatchResult(coord_res[2], mid_mideal, method, coord_res[0], coord_res[1], sArea_new*2, Math.min(mid_rect.width, mid_rect.height))) {
	    				
	    				
	    				if (refBitDepth==24 && !matchIntensity) {
	         				tmpIp = mid_tpl.duplicate();
	         				ImageConverter ic = new ImageConverter(tmpIp);
	                    	ic.convertToGray32();
	         			} else tmpIp=mid_tpl;
	        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mid, (int)coord_res[1]+ yStart_mid,tmpIp.getProcessor());
	        	        imageRoi.setOpacity(0.3);
	        	        overlay = new Overlay();
	        	        overlay.addElement(imageRoi);
	        			//imp.setSlice(slice);
	        			Roi rectroi = new Roi(xStart_mid, yStart_mid, sWX_mid, sWY_mid);
	        			rectroi.setStrokeWidth(3);
	        			rectroi.enableSubPixelResolution();
	        			overlay.addElement(rectroi);
	        			imp.setSlice(slice);
	        			imp.setOverlay(overlay);
	        			//IJ.showMessage("Not found in Area=" + sArea_new);
	    				
	    			} else {
	    				//IJ.showMessage("Found in Area = " + sArea_new);
	    				newmidPositionFound=true;
	    			}
		            
				}
     			
				if (!newmidPositionFound){
	     			overlay = new Overlay();
	     			
	     			if (refBitDepth==24 && !matchIntensity) {
	     				tmpIp = mid_tpl.duplicate();
	     				ImageConverter ic = new ImageConverter(tmpIp);
	                	ic.convertToGray32();
	     			} else tmpIp=mid_tpl;
	    			ImageRoi imageRoi = new ImageRoi((int)coord_res[0]+xStart_mid, (int)coord_res[1]+yStart_mid,tmpIp.getProcessor());
	    	        imageRoi.setOpacity(0.3);
	    	        overlay.addElement(imageRoi);
	    			imp.setSlice(slice);
	    			imp.setOverlay(overlay);
	    			//WindowManager.setCurrentWindow(imgWindow);
	    			//WindowManager.setWindow(imgWindow);
	    			//imp.setActivated();
	    			//imgWindow.toFront();
	    		
	    			
					int failureAnswer = failureQuestionDlg(2); 
					if (failureAnswer==0) adjustThreshold(coord_res[2], mid_mideal, method);
	    			ignoreFrame = (failureAnswer==1);
	    			stopTracking = (failureAnswer==2);
	    			reselectPoints = (failureAnswer==3);
				}
    		}
			
			if (ignoreFrame) return 1;
	        if (stopTracking) return 2;
	        if (reselectPoints) return 3;
     		

		
			if (iter>0) mid_matchRes.remove(mid_matchRes.size()-1);
			mid_matchRes.add(coord_res[2]);
			
			disX_mid = coord_res[0] + xStart_mid - mid_rect.x;
            disY_mid = coord_res[1] + yStart_mid - mid_rect.y;
            
            if (subPixel) {
            	
            	disX_mid += midRefCenterShiftX*(Math.cos(-mid_angle*Math.PI/180.0) - 1.0) + midRefCenterShiftY*Math.sin(-mid_angle*Math.PI/180.0);
            	disY_mid += midRefCenterShiftY*(Math.cos(-mid_angle*Math.PI/180.0) - 1.0) - midRefCenterShiftX*Math.sin(-mid_angle*Math.PI/180.0);
            }
            
            // current bending is computed and checked for the convergence
            calcBendingParams(false);
            if (Math.abs(disX_free-dxtmp)<1.0e-5 && Math.abs(disY_free-dytmp)<1.0e-5) break;
            dxtmp=disX_free;
            dytmp=disY_free;
        }
		
        
        
        // the creation time of the image is taken from the EXIF metadata or incremented by timeStep
        
        if (exifTime)
        {
        	Instant shot_time;
        	if(videoInput) shot_time = getShotTime("", slice);
        	else shot_time = getShotTime(imp.getOriginalFileInfo().directory + stack.getSliceLabel(slice), slice);
             
        	if (shot_time!=null) seconds = Duration.between(first_shot_time, shot_time).toNanos()/1000000000.0;//(new Duration(first_shot_time,shot_time)).getMillis()/1000.0;
        	else 
        	{	
        		exifTime=false;
        		if (seconds!=0.0) seconds+=timeStep;
        	}
        }
        else seconds+=timeStep;
		
        //slice_proc.translate(disX_holder, disY_holder);
		
        
		// Supposed central line of the bent crystal is plotted
		
        
        float[] xpf=new float[11], ypf=new float[11];
        for (int astep=0;astep<11;astep++)
        {
        	double ang=astep*bending_angle/10,
        			y=-(1.0-Math.cos(ang))/curvature,
        			x=Math.sin(ang)/curvature;
        	xpf[astep]=(float)(refX_att+disX_holder+Math.cos(deflection_angle)*x+Math.sin(deflection_angle)*y);
        	ypf[astep]=(float)(refY_att+disY_holder-Math.sin(deflection_angle)*x+Math.cos(deflection_angle)*y);
        	
        }
        PolygonRoi needle_line=new PolygonRoi(xpf,ypf,Roi.FREELINE);
        needle_line.setStrokeWidth(3);
        needle_line.enableSubPixelResolution();
        
        if (refBitDepth==24 && !matchIntensity) {
				tmpIp = free_tpl.duplicate();
				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
			} else tmpIp=free_tpl;
        ImageRoi imageRoi_free = new ImageRoi((int)disX_free+free_rect.x, (int)disY_free+free_rect.y,tmpIp.getProcessor());
        imageRoi_free.setOpacity(0.3);
        overlay = new Overlay(imageRoi_free);
        proi_free = new PointRoi(refX_free+disX_free,refY_free+disY_free);
        proi_free.setPointType(3);
        overlay.addElement(proi_free);
        overlay.addElement(needle_line);
        
        
        if (refBitDepth==24 && !matchIntensity) {
				tmpIp = mid_tpl.duplicate();
				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
			} else tmpIp=mid_tpl;
        ImageRoi imageRoi_mid = new ImageRoi((int)disX_mid+mid_rect.x, (int)disY_mid+mid_rect.y,tmpIp.getProcessor());
        imageRoi_mid.setOpacity(0.3);
        overlay.addElement(imageRoi_mid);
        proi_mid = new PointRoi(refX_mid+disX_mid,refY_mid+disY_mid);
        proi_mid.setPointType(3);
        overlay.addElement(proi_mid);
        
        Line hord_line =   new Line(refX_free + disX_free,
					        		refY_free + disY_free, 
					        		refX_att + disX_holder, 
					        		refY_att + disY_holder);
        hord_line.setStrokeWidth(3);
        hord_line.enableSubPixelResolution();
        overlay.addElement(hord_line);
        
        double x0 = (refX_free+disX_free+refX_att+disX_holder)/2.0,
			   y0 = (refY_free+disY_free+refY_att+disY_holder)/2.0,

			   x1,y1,
			   dx = -(refY_free+disY_free-(refY_att+disY_holder)),
			   dy = refX_free+disX_free-(refX_att+disX_holder),
			   dr = Math.sqrt(dx*dx+dy*dy),
			   dh = (1-Math.cos(curvature*cr_length/2.0))/curvature;
        
				dx/=dr;
				dy/=dr;
				
				x1 = x0 + dx*dh;
				y1 = y0 + dy*dh;

		Line mid_line = new Line(x1, y1, x0, y0);
		mid_line.setStrokeWidth(3);
		mid_line.enableSubPixelResolution();
        overlay.addElement(mid_line);
        
        
        
        
        // Overlays of the templates are placed over the obtained positions  
        if (refBitDepth==24 && !matchIntensity) {
				tmpIp = holder_ref.duplicate();
				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
			} else tmpIp=holder_ref;
        ImageRoi imageRoi_att = new ImageRoi((int)disX_holder+holder_rect.x, (int)disY_holder+holder_rect.y,tmpIp.getProcessor());
        imageRoi_att.setOpacity(0.3);
        overlay.addElement(imageRoi_att);
        proi_att = new PointRoi(refX_att+disX_holder,refY_att+disY_holder);
        proi_att.setPointType(3);
        overlay.addElement(proi_att);
        
        Roi holderroi = new Roi(xStart_holder, yStart_holder, sWX_holder, sWY_holder);
        holderroi.setStrokeWidth(3);
        holderroi.enableSubPixelResolution();
		overlay.addElement(holderroi);
        
		Roi midroi = new Roi(xStart_mid, yStart_mid, sWX_mid, sWY_mid);
        midroi.setStrokeWidth(3);
        midroi.enableSubPixelResolution();
		overlay.addElement(midroi);
		
		Roi freeroi = new Roi(xStart_free, yStart_free, sWX_free, sWY_free);
		freeroi.setStrokeWidth(3);
		freeroi.enableSubPixelResolution();
		overlay.addElement(freeroi);
		
       
		for(ImagePlus refBin : refBinaryFrames) {
        	ImageRoi ref_ImageRoi = new ImageRoi((int)disX_holder, (int)disY_holder,refBin.getProcessor());
	        ref_ImageRoi.setOpacity(0.2);
	        ref_ImageRoi.setZeroTransparent(true);
	        overlay.addElement(ref_ImageRoi);
        }
        
        
//        ImageRoi ref_ImageRoi = new ImageRoi((int)disX_holder, (int)disY_holder,refImageBinary.getProcessor());
//        ref_ImageRoi.setOpacity(0.3);
//        ref_ImageRoi.setZeroTransparent(true);
//        overlay.addElement(ref_ImageRoi);
		
        imp.setSlice(slice);
        imp.setOverlay(overlay);
        
        if (saveFlatten){
        	//FileSaver flattenSave = new FileSaver(imp.flatten());
        	FileInfo fi = imp.getOriginalFileInfo();
        	String directory = fi.directory + "flatten"+File.separatorChar;
        	saveFlattenFrames(directory, seconds, false);
        }
        
        
        
        return 0;
    }
    
    
    private void saveFlattenFrames(String directory, double seconds, boolean lastFrame) {
    	
    	


    	File theDir = new File(directory);

    	// if the directory does not exist, create it
    	if (!theDir.exists()) {


    		try{
    			theDir.mkdir();

    		} 
    		catch(SecurityException se){

    		}        

    	}

    	if (theDir.exists()) {
    		
    		if (!lastFrame) {
    			int frameNum = (int) Math.round(0.3*seconds);
    			FileSaver prevFlatten = new FileSaver(prevMovieFrame);
    			for (int frame_n=previousFrameNum; frame_n<frameNum; frame_n++) {
    				String frName = String.format("IMG_%05d.JPG", frame_n);
    				prevFlatten.saveAsJpeg(directory + frName);
    			}
    			
    			ImagePlus flatten_img = imp.flatten();
    			flatten_img.getProcessor().translate(-disX_holder, -disY_holder);
    			String paramInfo = String.format("1/R  = %.2E 1/pixel\ndL/L = %.2f %%", curvature, deformation*100.0);
    			TextRoi textoverlay = new TextRoi(50,50,paramInfo,fontParamInfo);
    			Overlay ov = new Overlay();  
    			ov.add(textoverlay);
    			flatten_img.setOverlay(ov);
    			
    			prevMovieFrame = new ImagePlus("",flatten_img.flatten().getProcessor().resize(720));
    			
    			previousFrameNum = frameNum;
    		} else {
    			String frName = String.format("IMG_%05d.JPG", previousFrameNum);
    			(new FileSaver(prevMovieFrame)).saveAsJpeg(directory + frName);
    		}
    	}
    }
    
    private void calcBendingParams(boolean reselect) {
    	
    	
    	
    	double H_x=refX_free+disX_free-(refX_att+disX_holder),
          	   H_y=refY_free+disY_free-(refY_att+disY_holder),
          	   H=Math.sqrt(H_x*H_x+H_y*H_y),
          	   cos_full_angle=H_x/H,
          	   
          	   H1_x=refX_mid+disX_mid-(refX_att+disX_holder),
               H1_y=refY_mid+disY_mid-(refY_att+disY_holder),
               H1=Math.sqrt(H1_x*H1_x+H1_y*H1_y),
               
               H2_x=refX_mid+disX_mid-(refX_free+disX_free),
               H2_y=refY_mid+disY_mid-(refY_free+disY_free),
               H2=Math.sqrt(H2_x*H2_x+H2_y*H2_y),
               
               H_mid_x=refX_mid+disX_mid-(refX_att+disX_holder+refX_free+disX_free)/2.0,
               H_mid_y=refY_mid+disY_mid-(refY_att+disY_holder+refY_free+disY_free)/2.0,
               sign=Math.signum(H_x*H_mid_y-H_y*H_mid_x);
    	
    	 full_angle=Math.acos(cos_full_angle);
         if (H_y>0.0) full_angle=-full_angle;
     	
        double cos_half_bend=(H*H-H1*H1-H2*H2)/2.0/H1/H2;
        if (cos_half_bend>=1.0) bending_angle=0.0;
        else if (cos_half_bend<=-1.0) bending_angle=2.0*Math.PI;
        else bending_angle=2.0*sign*Math.acos(cos_half_bend);
     	curvature=2.0*Math.sin(bending_angle/2.0)/H;
     	deflection_angle=full_angle-bending_angle/2.0;
     	if (curvature!=0.0) cr_length=Math.abs(bending_angle/curvature);
     	else cr_length=H;
     	if (length_ini==0.0) length_ini=cr_length;
     	if (reselect) {
     		
     		double  oldL0 = length_ini;
     		length_ini=cr_length/(1.0 + deform_list.get(deform_list.size()-1));
     		
     		IJ.showMessage("Initial length is changed from "+oldL0+ "\nto "+length_ini+"\nas the result of new selection");
     	}
        deformation=(cr_length-length_ini)/length_ini;
    }

 

	
    private boolean getUserParameters() {

        //boolean showFlattenOption = false;
    	
    	method =  (int) Prefs.get("BendingCrystalTrack.method", 5);
    	templSize=(int) Prefs.get("BendingCrystalTrack.templSize", 300);
    	sArea =   (int) Prefs.get("BendingCrystalTrack.sArea", 20);
    	subPixel =		Prefs.get("BendingCrystalTrack.subPixel", true);
    	matchIntensity =Prefs.get("BendingCrystalTrack.matchIntensity", true);
    	String[] methods = {"Square difference", "Normalized square difference", "Cross correlation", "Normalized cross correlation", "Correlation coefficient", "Normalized correlation coefficient"};
        //String[] itpMethods = {"Bilinear", "Bicubic"};

        GenericDialog gd = new GenericDialog(pluginName);
        gd.addMessage("Only virtual stacks of time lapse images are supported currently.\n"
        		+ "Adjust the settings and follow the instructions to select templates to track.");
        gd.addChoice("Matching method", methods, methods[method]);
        gd.addNumericField("Template rectangle size (rectangle ROI size in pixels) ", templSize, 0);
        //gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addNumericField("Search area(pixels around ROI) ", sArea, 0);
        gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addCheckbox("Subpixel registration", subPixel);
        gd.addCheckbox("Match RGB images using intensity", matchIntensity);
        //gd.addCheckbox("Save flatten copies of images with overlays", saveFlatten);
       
        //gd.addChoice("Interpolation method for subpixel translation", itpMethods, itpMethods[itpMethod]);
       
        //gd.addCheckbox("update templates?", false);
        
        Component[] gd_components = gd.getComponents();
        for (Component comp : gd_components)
        comp.addKeyListener(new KeyListener(){  

            @Override
            public void keyTyped(KeyEvent e) {
                
            }

            @Override
            public void keyPressed(KeyEvent e) {
            	
            	 if (gd.getComponentCount()==11 && e.isControlDown() && e.getKeyCode() == KeyEvent.VK_T) {
            		 //IJ.showMessage("Info", "pressed");
            		 //GenericDialog d = (GenericDialog)e.getSource();
            		 gd.addCheckbox("Save flatten copies of images with overlays", saveFlatten);
            		 gd.validate();
            		 gd.repaint();
            		 gd.pack();
            		 
                 } 
            }

            @Override
            public void keyReleased(KeyEvent e) {
                }
            });     
        
        
        gd.showDialog();
        if (gd.wasCanceled()) {
            return false;
        }
        method = gd.getNextChoiceIndex();
        templSize=(int) gd.getNextNumber();
        sArea = (int) gd.getNextNumber();
        subPixel = gd.getNextBoolean();
        matchIntensity  = gd.getNextBoolean();
        if (gd.getComponentCount()==12) saveFlatten = gd.getNextBoolean();
        
        
        Prefs.set("BendingCrystalTrack.method", method);
    	Prefs.set("BendingCrystalTrack.templSize", templSize);
    	Prefs.set("BendingCrystalTrack.sArea", sArea);
    	Prefs.set("BendingCrystalTrack.subPixel", subPixel);
    	Prefs.set("BendingCrystalTrack.matchIntensity", matchIntensity);
        //itpMethod = gd.getNextChoiceIndex();
        //updateTemplates = gd.getNextBoolean();
        showRT = true;

        return true;
    }
    /*
	public static IplImage toIplImage(BufferedImage bufImage) {

	    ToIplImage iplConverter = new OpenCVFrameConverter.ToIplImage();
	    Java2DFrameConverter java2dConverter = new Java2DFrameConverter();
	    IplImage iplImage = iplConverter.convert(java2dConverter.convert(bufImage));
	    return iplImage;
	}
	*/
	public static Mat toMatcv(BufferedImage bufImage) {

		Mat mat =  Java2DFrameUtils.toMat(bufImage);
//		OpenCVFrameConverter.ToMat matConverter = new OpenCVFrameConverter.ToMat();
//	    Java2DFrameConverter java2dConverter = new Java2DFrameConverter();
//	    Mat mat =  matConverter.convert(java2dConverter.convert(bufImage));
	    return mat;
	}
	

    
    public static double[]  doMatch_coord_res(ImageProcessor src, ImageProcessor tpl, int method, boolean subPix, double[] searchLine) {

        BufferedImage bi = null, bi2 = null;
        Mat sourceMat, templateMat, temp, temp2;
        int srcW = src.getWidth();
        int srcH = src.getHeight();
        int tplW = tpl.getWidth();
        int tplH = tpl.getHeight();
        sourceMat = null;
        templateMat = null;
        double[] coord_res = new double[3];
        
        switch (src.getBitDepth()) {
    
            case 16:
                //since cvMatchTemplate don't accept 16bit image, we have to convert it to 32bit
                bi = ((ShortProcessor) src).get16BitBufferedImage();
                temp = toMatcv(bi);
                temp.convertTo(sourceMat, CV_32FC1, 1 / 65535.0, 0);
                bi2 = ((ShortProcessor) tpl).get16BitBufferedImage();
                temp2 = toMatcv(bi2);
                temp2.convertTo(templateMat, CV_32FC1, 1 / 65535.0, 0);
                break;
            case 32:   
            case 24:	
            case 8:
            	
                bi = src.getBufferedImage();
                sourceMat = toMatcv(bi);

                bi2 = tpl.getBufferedImage();
                templateMat = toMatcv(bi2);

                break;
            default:
                IJ.error("Unsupported image type");
                break;
        }

       
        
        Mat resMat = new Mat(new Size(srcW - tplW + 1, srcH - tplH + 1), CV_32FC1);
        

        
        //CV_TM_SQDIFF        = 0,
        //CV_TM_SQDIFF_NORMED = 1,
        //CV_TM_CCORR         = 2,
        //CV_TM_CCORR_NORMED  = 3,
        //CV_TM_CCOEFF        = 4,
        //CV_TM_CCOEFF_NORMED = 5;
         

        ///
        /// This is the template matching function from the cv library 
        ///
       
        //cvMatchTemplate(iplSrc, iplTpl, res, method);
        matchTemplate(sourceMat, templateMat, resMat, method);
        
        //////Search the location of the template
        
        
        FloatIndexer resVal = resMat.createIndexer();
        if (searchLine!=null && !(searchLine[2]==0.0 && searchLine[3]==0.0)){  //////////////////// Searching the middle part along the normal line
        	
        	int[] coord = new int[2];
            coord[0]=0;
            coord[1]=0;
            double minmax=0.0;
            boolean firstPointFound=false;
            int sWh, sWw;
            sWh = resMat.rows();
            sWw = resMat.cols();
            double x0=searchLine[0], y0=searchLine[1], dx0=searchLine[2], dy0=searchLine[3];
            boolean searchMin = (method == 0 || method == 1);
            if (Math.abs(dx0)>Math.abs(dy0))
            {
            	for (int col = 0; col < sWw; col++) {
                	int row = (int)(y0 + dy0*(col-x0)/dx0);
                	if (row>=0 && row < sWh)
                	{
                		double val=resVal.get(row, col);
                		if (!firstPointFound) {
                			firstPointFound = true;
                			minmax=val;
                			coord[0] = col;
     	                    coord[1] = row;
                		}
    	                if ((searchMin && val < minmax) || (!searchMin && val > minmax)) {
    	                    minmax = val;
    	                    coord[0] = col;
    	                    coord[1] = row;
    	                }
                	}
                }
            	
            } else {
            	for (int row = 0; row < sWh; row++) {
                	int col = (int)(x0 + dx0*(row-y0)/dy0);
                	if (col>=0 && col < sWw)
                	{
                		double val=resVal.get(row, col);
                		if (!firstPointFound) {
                			firstPointFound = true;
                			minmax=val;
                			coord[0] = col;
     	                    coord[1] = row;
                		}
    	                if ((searchMin && val < minmax) || (!searchMin && val > minmax)) {
    	                    minmax = val;
    	                    coord[0] = col;
    	                    coord[1] = row;
    	                }
                	}
                }
            }
            coord_res[0] = coord[0];
        	coord_res[1] = coord[1];
        	coord_res[2] = minmax;
        	
        	if (subPix){
            	double dx, dy;
            	int x = (int)coord_res[0], y = (int)coord_res[1]; 
            	double lineAngle = Math.atan2(dy0, dx0), sin = Math.sin(lineAngle), cos = Math.cos(lineAngle);
                
                // border values
                if (x == 0
                        || x == resMat.cols() - 1
                        || y == 0
                        || y == resMat.rows() - 1) {
                    dx = 0.0;
                    dy = 0.0;
                } else {
                	
                	double fxx=resVal.get(y, x - 1) - 2.0 * resVal.get( y, x) + resVal.get(y, x + 1),
                		   fyy=resVal.get(y - 1, x) - 2.0 * resVal.get( y, x) + resVal.get(y + 1, x),
                		   fxy=(resVal.get(y + 1, x + 1) + resVal.get(y - 1, x - 1)
                		   		- resVal.get(y - 1, x + 1) - resVal.get(y + 1, x - 1))/4.0,
                		   fx=(resVal.get(y, x + 1) - resVal.get(y, x - 1))/2.0,
                		   fy=(resVal.get(y + 1, x) - resVal.get(y - 1, x))/2.0,
                		   fr=fx*cos + fy*sin,
                		   frr=fxx*cos*cos + fyy*sin*sin + fxy*sin*cos;
                	
                	if (frr==0.0) {
                		dx = 0.0;
                		dy = 0.0;
                	} else {
                		 dx = -fr/frr*cos;
                         dy = -fr/frr*sin;
                         if (Math.abs(dx)>1.0 || Math.abs(dy)>1.0) {
                        	dx = 0.0;
                     		dy = 0.0;
                         }
                	}
                		
                   
                }
                coord_res[0]+=dx;
                coord_res[1]+=dy;
            }
            
        	
        } else { /////////////////// Searching matching position inside the search area
        	DoublePointer minVal= new DoublePointer(0.0);
        	DoublePointer maxVal= new DoublePointer(0.0);
            Point min = new  Point();
            Point max = new  Point();
            minMaxLoc(resMat, minVal, maxVal, min, max, null);
            if (method == 0 || method == 1) {
            	coord_res[0] = min.x();
            	coord_res[1] = min.y();
            	coord_res[2] = minVal.get();
            } else {
            	coord_res[0] = max.x();
            	coord_res[1] = max.y();
            	coord_res[2] = maxVal.get();
            }
            
            if (subPix){
            	double dx, dy;
            	int x = (int)coord_res[0], y = (int)coord_res[1]; 
                
                // border values
                if (x == 0
                        || x == resMat.cols() - 1
                        || y == 0
                        || y == resMat.rows() - 1) {
                    dx = 0.0;
                    dy = 0.0;
                } else {
                	
                	double fxx=resVal.get(y, x - 1) - 2.0 * resVal.get( y, x) + resVal.get(y, x + 1),
                		   fyy=resVal.get(y - 1, x) - 2.0 * resVal.get( y, x) + resVal.get(y + 1, x),
                		   fxy=(resVal.get(y + 1, x + 1) + resVal.get(y - 1, x - 1)
                		   		- resVal.get(y - 1, x + 1) - resVal.get(y + 1, x - 1))/4.0,
                		   fx=(resVal.get(y, x + 1) - resVal.get(y, x - 1))/2.0,
                		   fy=(resVal.get(y + 1, x) - resVal.get(y - 1, x))/2.0;
                	double denom = fxy*fxy - fxx*fyy;
                	if (denom==0.0) {
                		dx = 0.0;
                		dy = 0.0;
                	} else {
                		 dx = (fyy*fx - fxy*fy)/denom;
                         dy = (fxx*fy - fxy*fx)/denom;
                         if (Math.abs(dx)>1.0 || Math.abs(dy)>1.0) {
                        	dx = 0.0;
                     		dy = 0.0;
                         }
                	}
                		
                   
                }
                coord_res[0]+=dx;
                coord_res[1]+=dy;
            }
        	
        }
        
        return coord_res;
    }
     
    public static double doMatch_test(ImageProcessor src, int method) {

    	
    	
    	
    	BufferedImage bi = null;
    	//bi = src.getBufferedImage();
    	//Mat sourceMat = toMatcv(bi);
    	
        Mat sourceMat, temp;
        sourceMat = null;
        
    	
    	switch (src.getBitDepth()) {
    	             
    	            case 16:
    	            	
    	                
    	                bi = ((ShortProcessor) src).get16BitBufferedImage();
    	                temp = toMatcv(bi);
    	                temp.convertTo(sourceMat, CV_32FC1, 1 / 65535.0, 0);
    	                break;
    	            case 32: 
    	            case 24:	
    	            case 8:
    	            	
    	                bi = src.getBufferedImage();
    	                sourceMat = toMatcv(bi);
    	                break;
    	            default:
    	                IJ.error("Unsupported image type");
    	                break;
    	        }
    	
    	
    	
        
       Size size = new Size(1, 1);
       Mat result = new Mat(size, CV_32FC1);
       matchTemplate(sourceMat, sourceMat, result, method);
       FloatIndexer idx = result.createIndexer(); 
       return idx.get(0);
       
    }
    


	@Override
	public boolean dialogItemChanged(GenericDialog arg0, AWTEvent arg1) {
		if (arg0.wasOKed() || arg0.wasCanceled()) folderMonitoring=true;
		
		return true;
	}
	
	
	
	
    
}
