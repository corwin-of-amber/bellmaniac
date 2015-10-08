rm -rf jarbin
cp -r out/production/Bellmania jarbin
cd jarbin
jar xf /opt/local/share/scala-2.11/lib/scala-library.jar
jar xf ../lib/mongo-java-driver-2.13.1.jar
echo "Main-Class: ui.CLI" > Manifest.txt
jar cfm ../bell.jar Manifest.txt .
