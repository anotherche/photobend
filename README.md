This is a Maven project implementing an ImageJ plugin providing tracking of 
a needle-like crystal shape changing during photobending process.
Photobending is a phenomenon of crystal deformation caused by non-uniform 
crystal structure transformation due to photochemical reaction. 

Required input is a stack of time lapse images taken during a photobending process.
The output is the time dependence of crystal's curvature and longitudinal deformation.
See details at http://imagej.net/PhotoBend

The project uses ideas and code of 
1. Template Matching by Qingzong Tseng (based on opencv)
2. javacv (java interface to OpenCV) by Samuel Audet 
3. Exif Metadata Library by Drew Noakes

