package Bending_Crystal_Track;

import ij.*;
import ij.process.*;
import ij.gui.*;
import ij.io.*;
import java.io.*;
//import java.util.*;

//import org.bytedeco.javacv.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacv.Java2DFrameConverter;
import org.bytedeco.javacv.OpenCVFrameConverter;
//import org.bytedeco.javacv.OpenCVFrameConverter.ToIplImage;
import org.bytedeco.javacv.OpenCVFrameConverter.ToMat;
import org.joda.time.DateTime;
import org.joda.time.Duration;


import com.drew.imaging.ImageMetadataReader;
//import com.drew.imaging.ImageProcessingException;
import com.drew.metadata.Metadata;
import com.drew.metadata.exif.ExifSubIFDDirectory;

import java.awt.*;


import ij.plugin.FolderOpener;
//import ij.plugin.*;
import ij.plugin.filter.*;
import ij.measure.ResultsTable;
import java.awt.image.BufferedImage;
//import java.nio.FloatBuffer;
import java.util.ArrayList;

import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
//import javax.swing.JTextField;

import static org.bytedeco.javacpp.opencv_core.*;
import static org.bytedeco.javacpp.opencv_imgproc.*;
import org.bytedeco.javacpp.indexer.*;
import org.bytedeco.javacpp.opencv_core.Mat;
import org.bytedeco.javacpp.opencv_core.Point;


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



public class cvBending_Crystal_Track implements PlugInFilter, DialogListener {

    ImagePlus imp, ref_Image, refImageBinary, free_ref, free_tpl, holder_ref, mid_ref, mid_tpl;

    GaussianBlur gaussianBlur;
    ImageStack stack;
    Rectangle free_rect, holder_rect, mid_rect;
    Roi free_roi,holder_roi,middle_roi;
    PointRoi proi_free,proi_att,proi_mid;
    int method=5, refSlice, sArea = 20, templSize=300;
    double seconds=0, timeStep=1.0;
    DateTime first_shot_time; 
    int width, height, refBitDepth, refX_free, refY_free, refX_att, refY_att, refX_mid, refY_mid;
    double disX_free, disY_free, disX_holder, disY_holder, disX_mid, disY_mid, rotAngle, disX_holder_save=0.0, disY_holder_save=0.0;
    double length_ini=0.0, cr_length, hord_ini,
    	   curvature_ini, curvature, 
    	   bending_angle_ini, bending_angle, 
    	   deflection_angle_ini, deflection_angle, 
    	   full_angle, full_angle_ini,
    	   initial_angle,
    	   deformation;
    double H0_x,H0_y;
    ArrayList<Double> curv_list, deform_list, time_list, freeEnd_matchRes, attEnd_matchRes, mid_matchRes ; 
    double curv_min=0.0, curv_max=0.0, def_min=0.0, def_max = 0.0;
    double free_mideal, att_mideal, mid_mideal;
    
    ImagePlus plotImage, plotDefImage;
    boolean folderMonitoring=true, updateTemplates=false, ExifTime=true;
    volatile WaitForUserDialog StopDlg=null, MonitorDlg=null;
    
    
    
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
        
        double std_length = (int) gd.getNextNumber();
        refX_att = refX_free + (int)(std_length*(refX_att - refX_free)/length_ini);
        refY_att = refY_free + (int)(std_length*(refY_att - refY_free)/length_ini);
        H0_x=refX_free-refX_att;
        H0_y=refY_free-refY_att;
        length_ini=Math.sqrt(H0_x*H0_x+H0_y*H0_y);
        hord_ini= length_ini;
        
        full_angle_ini=Math.acos(H0_x/hord_ini);
        if (refY_free>refY_att) full_angle_ini=-full_angle_ini;
        
        refX_mid = (refX_free + refX_att)/2;
        refY_mid = (refY_free + refY_att)/2;

        return true;

	}
	
    public int setup(String arg, ImagePlus imp) {
        this.imp = imp;
        
        return DOES_8G + DOES_16 +  DOES_32 + DOES_RGB + STACK_REQUIRED;
    }

    
	public void run(ImageProcessor ip) {

		
		imgWindow=imp.getWindow();
		
        stack = imp.getStack();
        if (!stack.isVirtual()) {
        	IJ.showMessage("Error", "only virtual stacks are supported");
            return;
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
		disX_free=0.0;
		disY_free=0.0;
		disX_holder=0.0;
		disY_holder=0.0;
		disX_mid=0.0;
		disY_mid=0.0;
		Overlay ov;

            if (!getUserParameters()) { return;
            }
            
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
            
            
            IJ.setTool("point");
            new WaitForUserDialog("Bending_Crystal_Track", "Select a point on the FREE needle's end...\nthen press OK.").show();
            
            proi_free = (PointRoi)imp.getRoi();
            if (proi_free!=null) {
            refX_free=proi_free.getPolygon().xpoints[0];
            refY_free=proi_free.getPolygon().ypoints[0];
            } else {
            	IJ.showMessage("Error", "point ROI needed");
                return;
            }
            
            int d1 = refX_free, d2 = width - refX_free, d3 = refY_free, d4 = height - refY_free;
            int dmin = Math.min(Math.min(d1, d2), Math.min(d3, d4));
            if (dmin<=sArea+1)
            {
            	IJ.showMessage("Error", "Search point is to close to the edge.\nReduce template rectangle size on the first dialog.");
                return;
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
            IJ.setTool("point");
            new WaitForUserDialog("Bending_Crystal_Track", "Select a point on the ATTACHED needle's end...\nthen press OK.").show();
            
            proi_att = (PointRoi)imp.getRoi();
            if (proi_att!=null) {
            refX_att=proi_att.getPolygon().xpoints[0];
            refY_att=proi_att.getPolygon().ypoints[0];
            } else {
            	IJ.showMessage("Error", "point ROI needed");
                return;
            }
            
            H0_x=refX_free-refX_att;
            H0_y=refY_free-refY_att;
            hord_ini=Math.sqrt(H0_x*H0_x+H0_y*H0_y);
            
            full_angle_ini=Math.acos(H0_x/hord_ini);
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
                 IJ.setTool("point");
                 new WaitForUserDialog("Bending_Crystal_Track", 
                		 "Select a point in the MIDDLE of the needle...\nthen press OK.").show();
                 
                 
                 proi_mid = (PointRoi)imp.getRoi();
                 if (proi_mid!=null) {
                 refX_mid=proi_mid.getPolygon().xpoints[0];
                 refY_mid=proi_mid.getPolygon().ypoints[0];
                 } else {
                 	IJ.showMessage("Error", "point ROI needed");
                     return;
                 }
                 
                
                 proi_mid.setPointType(3);
                 ov.addElement(proi_mid);
                 imp.setOverlay(ov);
            } 
            
            
            
            
            
            
            calcBendingParams();
            
            deflection_angle_ini=deflection_angle;
            bending_angle_ini=bending_angle;
            curvature_ini=curvature;
            initial_angle=full_angle_ini+0.5*bending_angle_ini;
            
            
            
            
            imp.killRoi();
            IJ.setTool("rect");
            new WaitForUserDialog("Bending_Crystal_Track", 
            		"Select a rectangle region around the stationary HOLDER edge.\n"//
            		+"A rectangle around a corner would be the best.\n"//
            		+"Press OK after the selection.").show();
            holder_roi=imp.getRoi();
            if (holder_roi != null && holder_roi.isArea()) {
                holder_rect = holder_roi.getBounds();
                
				
                
            } else {
                IJ.showMessage("Error", "rectangular ROI needed");
                return;
            }
            
            ov.addElement(holder_roi);
            imp.setOverlay(ov);
            
            ref_Image.setRoi(holder_roi);
            holder_ref=ref_Image.crop();
            if (matchIntensity) {
            	ImageConverter holder_ic = new ImageConverter(holder_ref);
            	holder_ic.convertToGray32();
            }
            gaussianBlur = new GaussianBlur();
            
            ImageProcessor ip_tmp=holder_ref.getProcessor();
            gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
            
            
           
           
             
            free_roi=new Roi(refX_free-rect_half_size,refY_free-rect_half_size,2*rect_half_size,2*rect_half_size);
            ref_Image.setRoi(free_roi);
            
            free_rect = free_roi.getBounds();
            free_rect.x+=(int)(free_rect.width*0.15);
            free_rect.y+=(int)(free_rect.height*0.15);
            free_rect.width=(int)(free_rect.width*0.7);
            free_rect.height=(int)(free_rect.height*0.7);
            
            free_ref = ref_Image.crop();
            if (matchIntensity) {
            	ImageConverter ic = new ImageConverter(free_ref);
            	ic.convertToGray32();
            }
            
            ip_tmp=free_ref.getProcessor();
            gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
            refCropRoi =  new Roi((int)(free_ref.getWidth()*0.15), (int)(free_ref.getHeight()*0.15), 
            							(int)(free_ref.getWidth()*0.7), (int)(free_ref.getHeight()*0.7));
		
		
            d1 = refX_mid;
            d2 = width - refX_mid;
            d3 = refY_mid;
            d4 = height - refY_mid;
            dmin = Math.min(Math.min(d1, d2), Math.min(d3, d4));
            if (dmin<=sArea+1)
            {
            	IJ.showMessage("Error", "Search point is to close to the edge");
                return;
            }
            
            rect_half_size=templSize/2;
            rect_hs_tmp = Math.max(rect_half_size, 0.7*rect_half_size+sArea);
            if (rect_hs_tmp>dmin)
            {
            	rect_half_size =(int) Math.min((dmin-sArea)/0.7, dmin);
            }
            
            middle_roi=new Roi(refX_mid-rect_half_size,refY_mid-rect_half_size,2*rect_half_size,2*rect_half_size);
            ref_Image.setRoi(middle_roi);
            
            mid_rect = middle_roi.getBounds();
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
            rt.showRowNumbers(false);

        }
        
        
        FileInfo fi = imp.getOriginalFileInfo();
        String directory = fi.directory;
        String name = stack.getSliceLabel(refSlice);
        first_shot_time = getShotTime(directory + name);
    	if (first_shot_time==null) ExifTime=false;
		
		
		
		
		
		if (showRT) {
            rt.incrementCounter();
            rt.addValue("Time", 0);
            rt.addValue("File", stack.getSliceLabel(refSlice));
            
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
            rt.showRowNumbers(false);
            
            
            
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
        
        
        Thread StopThread = new Thread(new Runnable()
		{
        	@Override
			public void run() 
			{
        		WaitForUserDialog dlg = new WaitForUserDialog("Tracking in progress...", "Close this message to stop the track");
        		dlg.setName("StopThread");
        		StopDlg=dlg;
        		dlg.show();
				
			}
		});
		StopThread.start();	
        
		
        
        for (int i = refSlice + 1; i < stack.getSize() + 1; i++) {     //align slices after reference slice.
        	
        	if (!StopThread.isAlive()) {
        		new WaitForUserDialog("Bending Crystal Track", "The track is finished.").show();
        		return;
        	}
        	
        	Opener opener = new Opener();  
			String imageFilePath = directory+stack.getSliceLabel(i);
			
			ImagePlus imp_new = opener.openImage(imageFilePath);
        	
			if ((new File(imageFilePath)).isFile() 
					&& imp_new!=null 
					&& imp_new.getWidth()==width 
					&& imp_new.getHeight()==height 
					&& imp_new.getBitDepth()==refBitDepth){

				
					double  tmp_disX_free=disX_free,
							tmp_disY_free=disY_free,
							tmp_disX_holder=disX_holder,
							tmp_disY_holder=disY_holder,
							tmp_disX_mid=disX_mid,
							tmp_disY_mid=disY_mid;
				    int matchresult = analyseSlice(i, stack.getProcessor(i));
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
						
						if (StopDlg!=null) {
				        	StopDlg.close();
				        	try {
								StopThread.join();
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
				        }
						return;
					}
		            
		            
		            
		            if (showRT) {
		            	rt.incrementCounter();
		            	
		                rt.addValue("Time", seconds);
		                rt.addValue("File", stack.getSliceLabel(i));
		                
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
		                rt.showRowNumbers(false);
		                
		           
		                
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
        	} else {
        		stack.deleteSlice(i--);
        		imp.setStack(stack);
        	}
            
        }
       
        
        
        if (StopDlg!=null) {
        	StopDlg.close();
        	try {
				StopThread.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        }
        	
        
       
        
        GenericDialog gd = new GenericDialog("Monitor for additional images");
        gd.addMessage("Do you want to check/monitor the folder for additional images?");
        gd.showDialog();
        if (gd.wasCanceled()) return;
        
        
        Thread monitorThread = new Thread(new Runnable()
		{
        	@Override
			public void run() 
			{
        		WaitForUserDialog dlg = new WaitForUserDialog("Waiting for new images...", "Press OK to stop monitoring the folder");
				
				
        		dlg.setName("MonitorThread");
        		MonitorDlg=dlg;
        		dlg.show();
				
			}
		});
		monitorThread.start();	
		
		synchronized (this){
			try {
				this.wait(2000);
				} catch (InterruptedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
		}
			
	        while (monitorThread.isAlive()) {
	        	
	            
	        	
	            	File[] fileList = (new File(directory)).listFiles();
	            	if (fileList != null) {
	            		
		
		            	// Exclude directories
		            	String[] tmplist = new String[fileList.length];
		            	
		            	
		            	int c = 0;
		            	for (int i = 0; i < fileList.length; i++)
		            		if (fileList[i].isFile())
		            			tmplist[c++] = fileList[i].getName();
		            	if (c>0) {
			            	String[] list = new String[c];
			            	for (int i = 0; i < c; i++) list[i] = tmplist[i];
			            	
			
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
				            					
				            					if (!monitorThread.isAlive()) break;
				            					
				            					Opener opener = new Opener();  
				            					String imageFilePath = directory+imageList[j];
				            					ImagePlus imp_new = opener.openImage(imageFilePath);
				            					if (imp_new!=null 
				            							&& imp_new.getWidth()==width 
				            							&& imp_new.getHeight()==height 
				            							&& imp_new.getBitDepth()==refBitDepth){
				            						
				            		        		vstack.addSlice(imageList[j]);
					            					
					            					imp.setStack(vstack);
					            					
					            					imp.setSlice(vstack.getSize());
					            					
					            					
					            					double  tmp_disX_free=disX_free,
					            							tmp_disY_free=disY_free,
					            							tmp_disX_holder=disX_holder,
					            							tmp_disY_holder=disY_holder,
					            							tmp_disX_mid=disX_mid,
					            							tmp_disY_mid=disY_mid;
					            				    			            					
					            					int matchresult = analyseSlice(vstack.getSize(),imp_new.getProcessor());
					            						
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
					            							if (MonitorDlg!=null) {
					            					        	MonitorDlg.close();
					            					        	try {
					            									monitorThread.join();
					            								} catch (InterruptedException e) {
					            									// TODO Auto-generated catch block
					            									e.printStackTrace();
					            								}
					            					        }
					            							return;
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
						            		                rt.showRowNumbers(false);
						            		                
						            		               
						            		                
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
        new WaitForUserDialog("Bending Crystal Tracking", "The tracking is finished.").show();
    }
	
	private DateTime getShotTime(String imageFilePath)
	{
		 // the creation time of the image is taken from the EXIF metadata
        
	       
		File jpegFile = new File(imageFilePath);
		
		Metadata metadata;
		
		try {
			metadata = ImageMetadataReader.readMetadata(jpegFile);
			ExifSubIFDDirectory md_directory = metadata.getFirstDirectoryOfType(ExifSubIFDDirectory.class);
		    return new DateTime(md_directory.getDateOriginal());
			
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
        "Stop tracking" };
		String placeName = (place==0?"holder":(place==1?"free end":"middle part"));  
		JPanel panel = new JPanel();
		panel.add(new JLabel("<html>Match of the "+placeName+" is poor."
				+ "<br>Select one of the possibilities:"
				+ "<br>1. Accept the match and continue"
				+ "<br>2. Skip this frame and continue"
				+ "<br>3. Stop the tracking</html>"));
		

		imgWindow.toFront();
		int result = JOptionPane.showOptionDialog(null, panel, "Match is poor",
        JOptionPane.YES_NO_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE,
        null, options1, null);
		if (result== JOptionPane.YES_OPTION) return 0;
		if (result== JOptionPane.NO_OPTION) return 1;
		return 2;
	}

    private int analyseSlice(int slice, ImageProcessor slice_proc) {

 
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
        
        boolean ignoreFrame=false, stopTracking=false;
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
        	}
        }
        
        if (ignoreFrame) return 1;
        if (stopTracking) return 2;
        
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
    			tpl_ip.setInterpolationMethod(ImageProcessor.BILINEAR);
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
    				}
        		}
    			
    			if (ignoreFrame) return 1;
    	        if (stopTracking) return 2;
 
    	        if (iter>0) freeEnd_matchRes.remove(freeEnd_matchRes.size()-1);
    			freeEnd_matchRes.add(coord_res[2]);
    			
    			disX_free = coord_res[0] + xStart_free - free_rect.x;
                disY_free = coord_res[1] + yStart_free - free_rect.y;
    			

            
            
            mid_tpl = mid_ref.duplicate();
			
			ImageProcessor mid_ip = mid_tpl.getProcessor();
			mid_ip.setInterpolationMethod(ImageProcessor.BILINEAR);
		
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
	        			
	        			overlay.addElement(new Roi(xStart_mid, yStart_mid, sWX_mid, sWY_mid));
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
				}
    		}
			
			if (ignoreFrame) return 1;
	        if (stopTracking) return 2;
     		

		
			if (iter>0) mid_matchRes.remove(mid_matchRes.size()-1);
			mid_matchRes.add(coord_res[2]);
			
			disX_mid = coord_res[0] + xStart_mid - mid_rect.x;
            disY_mid = coord_res[1] + yStart_mid - mid_rect.y;
            
            // current bending is computed and checked for the convergence
            calcBendingParams();
            if (Math.abs(disX_free-dxtmp)<1.0e-5 && Math.abs(disY_free-dytmp)<1.0e-5) break;
            dxtmp=disX_free;
            dytmp=disY_free;
        }
		
		
        
        // the creation time of the image is taken from the EXIF metadata or incremented by timeStep
        
        if (ExifTime)
        {
             DateTime shot_time = getShotTime(imp.getOriginalFileInfo().directory + stack.getSliceLabel(slice));
             
        	if (shot_time!=null) seconds = (double)((new Duration(first_shot_time,shot_time)).getStandardSeconds());
        	else 
        	{	
        		ExifTime=false;
        		if (seconds!=0.0) seconds+=timeStep;
        	}
        }
        else seconds+=timeStep;
		
		
		
        
		// Supposed central line of the bent crystal is plotted
		
        
        float[] xpf=new float[11], ypf=new float[11];
        for (int astep=0;astep<11;astep++)
        {
        	double ang=astep*bending_angle/10,
        			y=-(1.0-Math.cos(ang))/curvature,
        			x=Math.sin(ang)/curvature;
        	xpf[astep]=refX_att+(float)disX_holder+(float)(Math.cos(deflection_angle)*x+Math.sin(deflection_angle)*y);
        	ypf[astep]=refY_att+(float)disY_holder+(float)(-Math.sin(deflection_angle)*x+Math.cos(deflection_angle)*y);
        	
        }
        PolygonRoi needle_line=new PolygonRoi(xpf,ypf,Roi.FREELINE);
        
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
        overlay.addElement(new Roi(xStart_holder, yStart_holder, sWX_holder, sWY_holder));
        overlay.addElement(new Roi(xStart_mid, yStart_mid, sWX_mid, sWY_mid));
        overlay.addElement(new Roi(xStart_free, yStart_free, sWX_free, sWY_free));
        
        
        
        ImageRoi ref_ImageRoi = new ImageRoi((int)disX_holder, (int)disY_holder,refImageBinary.getProcessor());
        ref_ImageRoi.setOpacity(0.3);
        ref_ImageRoi.setZeroTransparent(true);
        overlay.addElement(ref_ImageRoi);
        
        imp.setSlice(slice);
        imp.setOverlay(overlay);
 
        return 0;
    }
    
    private void calcBendingParams() {
    	
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
     	
     	bending_angle=2.0*sign*Math.acos((H*H-H1*H1-H2*H2)/2.0/H1/H2); 
     	curvature=2.0*Math.sin(bending_angle/2.0)/H;
     	deflection_angle=full_angle-bending_angle/2.0;
     	if (curvature!=0.0) cr_length=Math.abs(bending_angle/curvature);
     	else cr_length=H;
     	if (length_ini==0.0) length_ini=cr_length;
        deformation=(cr_length-length_ini)/length_ini;
    }

 

	
    private boolean getUserParameters() {

        String[] methods = {"Square difference", "Normalized square difference", "Cross correlation", "Normalized cross correlation", "Correlation coefficient", "Normalized correlation coefficient"};
        //String[] itpMethods = {"Bilinear", "Bicubic"};

        GenericDialog gd = new GenericDialog("Bending Crystal Track");
        gd.addMessage("Only virtual stacks of time lapse images are supported currently.\n"
        		+ "Adjust the settings and follow the instructions to select templates to track.");
        gd.addChoice("Matching method", methods, methods[5]);
        gd.addNumericField("Template rectangle size (rectangle ROI size in pixels) ", 300, 0);
        //gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addNumericField("Search area(pixels around ROI) ", 20, 0);
        gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addCheckbox("Subpixel registration.", subPixel);
        gd.addCheckbox("Match RGB images using intensity.", matchIntensity);
        //gd.addChoice("Interpolation method for subpixel translation", itpMethods, itpMethods[itpMethod]);
       
        //gd.addCheckbox("update templates?", false);
        gd.showDialog();
        if (gd.wasCanceled()) {
            return false;
        }
        method = gd.getNextChoiceIndex();
        templSize=(int) gd.getNextNumber();
        sArea = (int) gd.getNextNumber();
        subPixel = gd.getNextBoolean();
        matchIntensity  = gd.getNextBoolean();
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

	    
	    ToMat matConverter = new OpenCVFrameConverter.ToMat();
	    Java2DFrameConverter java2dConverter = new Java2DFrameConverter();
	    Mat mat =  matConverter.convert(java2dConverter.convert(bufImage));
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
