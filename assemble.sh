rm -rf jarbin
cp -r bin jarbin
cd jarbin
jar xf /opt/local/share/scala-2.11/lib/scala-library.jar
jar xf /opt/local/share/scala-2.11/lib/scala-reflect.jar
jar xf ../lib/mongo-java-driver-2.13.1.jar
tar xf ../lib/scallop_2.11-0.9.5.jar
tar xf $Z3/com.microsoft.z3.jar
echo "Main-Class: ui.CLI" > Manifest.txt
jar cfm ../bell.jar Manifest.txt .

cd ..
jar cf ccg.jar -C bin synth/tactics/sketch/
