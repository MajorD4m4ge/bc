# = 'khanta'
#TODO Check different filesizes and files
#TODO Check filename reading in directory
#TODO TimeDate Stamp MS and Accessed Day
#TODO Error checking on Volume
#TODO Windows won't work.
#TODO Add marking clusters as bad
#TODO Rework command line args
#Create Disk  --> dd if=/dev/zero of=512MB.dd bs=1M count=512
#Create FAT32 --> mkdosfs -n 512MB -F 32 -v 512MB.dd
import os
import sys
import argparse
import datetime
import signal
import struct
import hashlib
import zlib, lzma, gzip
from array import array
from sys import platform as _platform
import ntpath

debug = 0
#References Microsoft's FAT General Overview 1.03
# <editor-fold desc="Boot Sector Variables">

BytesPerSector = ''  #Offset 11 - 2 bytes
SectorsPerCluster = ''  #Offset 13 - 1 byte
ReservedSectorCount = ''  #Offset 14 - 2 bytes
NumberOfFATs = ''  #Offset 16 - 1 byte
TotalSectors = ''  #Offset 32 - 4 bytes
# Start of FAT32 Structure 
FAT32Size = ''  #Offset 36 - 4 bytes
RootCluster = ''  #Offset 44 - 4 bytes
FSInfoSector = ''  #Offset 48 - 2 bytes
ClusterSize = ''
TotalFAT32Sectors = ''
TotalFAT32Bytes = ''
DataAreaStart = ''
DataAreaEnd = ''
RootDirSectors = 0  #Always 0 for Fat32 Per MS Documentation
#FSINFO 
Signature = ''
NumberOfFreeClusters = 0
NextFreeCluster = 0
BootSectorSize = 512
# </editor-fold>

# <editor-fold desc="Global Variables">
FirstChar = ''
EightDotThree = ''
FileAttributes = ''
CreatedTimeTenths = ''
CreateTimeHMS = ''
CreateDay = ''
AccessDay = ''
WrittenTimeHMS = ''
WrittenDay = ''
SizeOfFile = ''
FileSize = 0
HighTwoBytesFirst = ''
LowTwoBytesFirst = ''
FreeDirOffset = ''
#EndOfChain = 0xfffffff8
EndOfChain = 0x0fffffff
EndOfFile = 0x0fffffff
EmptyCluster = 0x00000000
DamagedCluster = 0x0ffffff7
ValidBytesPerSector = [512, 1024, 2048, 4096]

TotalChunks = 0  #The total clusters that need to be written. This will be int * remainder
FirstCluster = 0  #The first cluster.  This is written to the RootDir
ChunkList = []
ReadClusterList = []
MD5HashValue = ''
FileName = ''
FileData = ''
SkippedClusters = ''

# </editor-fold>


def HashMD5(file, block_size=2 ** 20):
    if (debug >= 1):
        print('Entering HashMD5:')
    md5 = hashlib.md5()
    with open(file, 'rb') as f:
        while True:
            data = f.read(block_size)
            if not data:
                break
            md5.update(data)
    return md5.hexdigest()


def GetDate():
    if (debug >= 1):
        print('Entering GetDate:')
    dtm = datetime.datetime.now()
    #dtm = datetime.datetime.now()
    i_year = int((dtm.year - 1980) << 9)
    i_month = int((dtm.month) << 5)
    i_day = int((dtm.day & 0x1F))
    i_hour = int((dtm.hour) << 11)
    i_min = int((dtm.minute) << 5)
    i_sec = int(dtm.second) / 2
    i_ms = int(dtm.microsecond)
    i_lo = int((int(i_year) | int(i_month)) | int(i_day))
    i_hi = int((int(i_hour) | int(i_min)) | int(i_sec))
    low = struct.pack("<H", i_lo)
    high = struct.pack("<H", i_hi)
    #ms = struct.pack("h", i_ms)
    if (debug >= 2):
        print('MS:HH:MM:SS:DD - ' + str(high) + str(low))
    return high + low


def GetDay():
    if (debug >= 2):
        print('Entering GetDay:')
    dtm = datetime.datetime.now()
    i_day = int((dtm.day) & 0x1F)
    day = struct.pack(">i", i_day)
    if (debug >= 2):
        print('Day: ' + str(day))
    return day


def GetHighBytes(number):
    if (debug >= 2):
        print('Entering GetHighBytes:')
    highbytes = (number & 0xffff0000)
    if (debug >= 2):
        print('\tHigh Bytes: ' + str(highbytes))
    return highbytes


def GetLowBytes(number):
    if (debug >= 2):
        print('Entering GetLowBytes:')
    lowbytes = (number & 0x0000ffff)
    if (debug >= 2):
        print('\tLow Bytes: ' + str(lowbytes))
    return lowbytes


def FileNamePad(file):
    status = True
    error = ''
    global FileName

    try:
        if (debug >= 1):
            print('Entering FileNamePad:')
        if (debug >= 2):
            print('\tFilename Passed in: ' + str(file))
        padding = 0
        extpad = 0
        extension = ''
        length = len(file)
        if (length == 12):
            if "." in str(file):
                filename = file.replace('.', '')
                filename = filename.encode('ascii').upper()
                if (debug >= 2):
                    print('\tFilename is 8.3 --> ' + str(filename))
                FileName = filename
            else:
                error = 'Long Filenames not Supported.'
        else:
            if (length > 12):
                error = 'Long Filenames not Supported.'
            else:
                if "." in str(file):
                    if (debug >= 2):
                        print('\tFilename has Period in it. -->' + str(file))
                    parts = file.split('.')
                    extension = parts[1]
                    if (len(extension) < 3):
                        extpad = 3 - len(extension)
                    extension = extension.encode('ascii').upper()
                    extension += extpad * b'\x20'
                    filename = parts[0]
                    if (debug >= 2):
                        print('\tExtension: ' + str(extension))
                        print('\tFile: ' + str(filename))
                    if (len(filename) < 8):
                        padding = 8 - len(filename)
                        if (debug >= 2):
                            print('\tFilename and Length - ' + str(filename) + ' : ' + str(padding))
                        filename = filename.encode('ascii').upper()
                        filename += padding * b'\x20'
                    else:
                        filename = file.encode('ascii').upper()
                else:
                    if (debug >= 2):
                        print('\tFilename does not have period in it. -->' + str(file))
                    if (len(file) < 11):
                        padding = 11 - len(file)
                    filename = file.encode('ascii').upper()
                    filename += padding * b'\x20'
                    FileName = filename
        if not (extension == ""):
            #extension = extension.encode('ascii').upper()
            filename = filename + extension
            FileName = filename
            if (debug >= 2):
                print('\tFilename Length/Padding Length: ' + str(len(file)) + '/' + str(padding))
                print('\tFilename: ' + str(filename))
        else:
            if (debug >= 2):
                print('\tFilename Length/Padding Length: ' + str(len(file)) + '/' + str(padding))
                print('\tFilename: ' + str(filename))
        FileName = filename
    except:
        status = False
    finally:
        return status, error


def ReadBootSector(volume):
    # <editor-fold desc="Global Variables">
    global DataAreaStart
    global BytesPerSector
    global SectorsPerCluster
    global ReservedSectorCount
    global NumberOfFATs
    global TotalSectors
    # Start of FAT32 Structure
    global FAT32Size
    global RootCluster
    global FSInfoSector
    global ClusterSize
    global BootSector
    global TotalFAT32Sectors
    global TotalFAT32Bytes
    global DataAreaStart
    global DataAreaEnd
    global FirstDataSector
    # </editor-fold>
    status = True
    error = ''

    # Reads the specified bytes from the drive
    try:
        if (debug >= 1):
            print('Entering ReadBootSector:')
        with open(volume, "rb") as f:
            bytes = f.read(BootSectorSize)
            BytesPerSector = struct.unpack("<H", bytes[11:13])[0]
            if (BytesPerSector not in ValidBytesPerSector):
                print('Error: This is not a FAT32 drive.')
            SectorsPerCluster = struct.unpack("<b", bytes[13:14])[0]
            ReservedSectorCount = struct.unpack("<H", bytes[14:16])[0]
            NumberOfFATs = struct.unpack("<b", bytes[16:17])[0]
            TotalSectors = struct.unpack("i", bytes[32:36])[0]
            FAT32Size = struct.unpack("i", bytes[36:40])[0]
            RootCluster = struct.unpack("i", bytes[44:48])[0]
            FSInfoSector = struct.unpack("<H", bytes[48:50])[0]

            #Calculate some values
            ClusterSize = SectorsPerCluster * BytesPerSector
            TotalFAT32Sectors = FAT32Size * NumberOfFATs
            TotalFAT32Bytes = FAT32Size * BytesPerSector

            DataAreaStart = ReservedSectorCount + TotalFAT32Sectors
            DataAreaEnd = TotalSectors - 1  #Base 0
            #Double Check per MS Documentation
            #FirstDataSector = BPB_ReservedSecCnt + (BPB_NumFATs * FATSz) + RootDirSectors;
            FirstDataSector = ReservedSectorCount + (NumberOfFATs * FAT32Size) + RootDirSectors
            if (debug >= 1):
                print('\tBytes per Sector: ' + str(BytesPerSector))
                print('\tSectors per Cluster: ' + str(SectorsPerCluster))
                print('\tCluster Size: ' + str(ClusterSize))
                print('\tRoot Cluster: ' + str(RootCluster))
                print('\tFSInfo Cluster: ' + str(FSInfoSector))
                print('\tTotal Sectors: ' + str(TotalSectors))
                print('\tReserved Sector Count: ' + str(ReservedSectorCount))
                print('\tReserved Sectors: ' + '0  - ' + str(ReservedSectorCount - 1))
                print('\tFAT Offset: ' + str(ReservedSectorCount))
                print('\tFAT Offset (Bytes): ' + str(ReservedSectorCount * BytesPerSector))
                print('\tNumber of FATs: ' + str(NumberOfFATs))
                print('\tFAT32 Size: ' + str(FAT32Size))
                print('\tTotal FAT32 Sectors: ' + str(TotalFAT32Sectors))
                print('\tFAT Sectors: ' + str(ReservedSectorCount) + ' - ' + str(
                    (ReservedSectorCount - 1) + (FAT32Size * NumberOfFATs)))
                print('\tData Area: ' + str(DataAreaStart) + ' - ' + str(DataAreaEnd))
                print('\tData Area Offset (Bytes): ' + str(DataAreaStart * BytesPerSector))
                #print('\tRoot Directory: ' + str(DataAreaStart) + ' - ' + str(DataAreaStart + 3))
                #Extra Testing
                print('\t   First Data Sector: ' + str(FirstDataSector))
    except IOError:
        status = False
        error = 'Volume ' + str(volume) + ' does not exist.'
    except:
        status = False
        error = 'Cannot read Boot Sector.'
    finally:
        return status, error


def GetFSInfo(volume):
    status = True
    error = ''
    global NumberOfFreeClusters

    try:
        if (debug >= 1):
            print('Entering GetFSInfo:')
        #Number of Free Clusters - 488-491
        #Next Free Cluster 492-495
        with open(volume, "rb") as f:
            f.seek(FSInfoSector * BytesPerSector + 488)
            temp = f.read(4)
            NumberOfFreeClusters = struct.unpack("<i", temp)[0]
            if (debug >= 2):
                print('\tNumber of Free Clusters: ' + str(struct.unpack("<i", temp)[0]))
            f.seek(FSInfoSector * BytesPerSector + 492)
            NextFreeCluster = f.read(4)
            if (debug >= 2):
                print('\tNext Free Cluster: ' + str(struct.unpack("<i", NextFreeCluster)[0]))
    except:
        status = False
        error = 'Cannot read FSInfo'
    finally:
        return (status, error)


def GetNextFreeCluster(volume):
    status = True
    error = ''

    try:

        if (debug >= 1):
            print('Entering GetNextFreeCluster:')
        global NextFreeCluster
        clusternumber = 0
        x = 0
        with open(volume, "rb") as f:
            f.seek(ReservedSectorCount * BytesPerSector)  #Remember to multiply by 512 to get bytes
            bytes = f.read(TotalFAT32Bytes)  #Read a copy of the FAT Table
            #for u in range(0, chunks):
            while (True):
                temp = (bytes[x:x + 4])
                if (temp == b'\x00\x00\x00\x00'):
                    if (debug >= 2):
                        print('\tFree Cluster - Byte Offset: ' + str((ReservedSectorCount * BytesPerSector) + x))
                        print('\tFree Cluster Number: ' + str(clusternumber))
                    freecluster = clusternumber
                    break
                else:
                    x += 4
                    clusternumber += 1
        NextFreeCluster = freecluster
    except:
        error = 'Cannot calculate next free cluster.'
        status = False
    finally:
        return status, error


def GetFileSize(file):
    if (debug >= 2):
        print('Entering GetFileSize:')
    size = os.path.getsize(file)  #Return length of file
    if (debug >= 2):
        print('\tFilesize: ' + str(size))
    return size


def MinFileLength(file, fragments):
    if (GetFileSize(file) < BytesPerSector * SectorsPerCluster * fragments + 1 ):
        return False
    else:
        return True


def GetOffsetFromCluster(FATOffset, cluster):  #FATOffset is ReservedSectorCount
    if (debug >= 2):
        print('Entering GetOffsetFromCluster:')
    temp = ((FATOffset * BytesPerSector) + ((cluster) * 4))
    if (debug >= 2):
        print('\tFAT Offset: ' + str(FATOffset))
        print('\tFAT Offset (Bytes:) ' + str(FATOffset * BytesPerSector))
        print('\tCluster: ' + str(cluster) + ' - Offset (Bytes): ' + str(temp))
    return (temp)


def GetChunks(file):
    status = True
    error = ''
    global TotalChunks

    try:
        if (debug >= 1):
            print('Entering GetChunks:')
        totalchunks = (int)(GetFileSize(file) / ClusterSize)
        remainderbytes = GetFileSize(file) % ClusterSize
        if (remainderbytes == 0):  #Checks if there is a remainder, if so add an extra chunk to total
            if (totalchunks == 0):  #Fits in one cluster
                totalchunks = 1
            TotalChunks = totalchunks
        else:
            TotalChunks = totalchunks + 1
        if (debug >= 2):
            print('\t' + str(totalchunks) + ' - ' + str(ClusterSize) + ' byte chunks.')
            print('\tRemainder Bytes: ' + str(remainderbytes))
            print('\tOriginal File Size: ' + str(GetFileSize(file)))
            print('\tTotal Bytes to be Written: ' + str(totalchunks * ClusterSize + remainderbytes))
            print('\tTotal Chunks: ' + str(TotalChunks))
    except:
        error = ('Cannot Calculate Fragments.')
        status = False
    finally:
        return status, error


def ReadFat(volume, chunks):  #Passes in the volume and chunks that need to written
    status = True
    error = ''
    global ChunkList
    global FirstCluster
    global TotalFreeClusters
    global NumberOfFreeClusters
    global SkippedClusters

    try:
        if (debug >= 1):
            print('Entering ReadFat:')
            print('\tChunks passed in: ' + str(chunks))
        x = 0
        with open(volume,
                  "rb") as f:  #Opens the file for reading/writing http://www.tutorialspoint.com/python/python_files_io.htm
            f.seek(ReservedSectorCount * BytesPerSector)  #Remember to multiply by 512 to get bytes
            bytes = f.read(TotalFAT32Bytes)  #Read a copy of the FAT Table
            clusternumber = 0

            #for u in range(0, chunks):
            while (chunks != 0):
                temp = (bytes[x:x + 4])
                if (debug >= 2):
                    print('\tBytes Found: ' + str(x) + ':' + str(temp))
                    print('\tCluster Offset: ' + str(clusternumber))  #Clusters start at 2 , so add 2 to iterator
                if (temp == b'\x00\x00\x00\x00'):
                    if (debug >= 2):
                        print('\tFree Cluster - Byte Offset: ' + str((ReservedSectorCount * BytesPerSector) + x))
                    ChunkList.append(clusternumber)
                    chunks -= 1
                x += 4
                clusternumber += 1
            if (debug >= 1):
                print('\tCluster List [Total]: ' + '[' + str(len(ChunkList)) + ']' + (str(ChunkList)))

            FirstCluster = ChunkList[0]
            if (debug >= 2):
                print('\tNumber of Free Clusters - Number Used (' + str(NumberOfFreeClusters) + ' - ' + str(
                    len(ChunkList)) + ')' + '= ' + str(NumberOfFreeClusters - len(ChunkList)))
            NumberOfFreeClusters = NumberOfFreeClusters - len(ChunkList)
            if (debug >= 1):
                print('\tFirst Cluster: ' + (str(FirstCluster)))
                print(
                    '\tFirst Cluster Offset (Bytes:) ' + str(
                        ((ReservedSectorCount * BytesPerSector) + ((FirstCluster - 1) * 4))))
    except:
        error = ('Error: Cannot read FAT.')
        status = False
    finally:
        return status, error


def find_missing_range(numbers, min, max):
    expected_range = set(range(min, max + 1))
    return sorted(expected_range - set(numbers))


def numbers_as_ranges(numbers):
    ranges = []
    for number in numbers:
        if ranges and number == (ranges[-1][-1] + 1):
            ranges[-1] = (ranges[-1][0], number)
        else:
            ranges.append((number, number))
    return ranges


def format_ranges(ranges):
    range_iter = (("%d" % r[0] if r[0] == r[1] else "%d-%d" % r) for r in ranges)
    return "(" + ", ".join(range_iter) + ")"


def WriteFAT(volume, clusterlist):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering WriteFAT:')
        #clusterlist.pop(0) #Remove first entry in the clusterlist as that is the "First Cluster"
        if (debug >= 1):
            print('\tCluster List: ' + str(clusterlist))
        with open(volume,
                  "rb+") as f:  #Opens the file for reading/writing http://www.tutorialspoint.com/python/python_files_io.htm
            f.seek(ReservedSectorCount * BytesPerSector + (
            (FirstCluster - 1) * 4))  #Remember to multiply by 512 to get bytes
            if (debug >= 1):
                print('\tSeeking to First Cluster Offset (Bytes): ' + str(
                    ReservedSectorCount * BytesPerSector + ((FirstCluster - 1) * 4)))
            for cluster in clusterlist:
                c = struct.pack("I", DamagedCluster)
                f.write(c)
                #f.seek(GetOffsetFromCluster(ReservedSectorCount, cluster))
                #f.write(struct.pack("I", EndOfChain))
    except:
        error = 'Error: Cannot read Write FAT.'
        status = False
    finally:
        return status, error


def WriteData(volume, file, clusterlist):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering WriteData:')
        chunk = ''
        with open(volume, "rb+") as f:
            if (debug >= 1):
                print('Opening Volume: ' + str(volume))
            with open(file, "rb") as r:
                if (debug >= 1):
                    print('\tReading file: ' + str(ntpath.basename(file)))
                for cluster in clusterlist:  #New Offset is 2 (Cluster)
                    seeker = (cluster * ClusterSize + (DataAreaStart * BytesPerSector) - 2 * ClusterSize)
                    f.seek(seeker)  #Each ClusterNum - 2 (Offset) * Bytes per cluster + (DataAreaStart * 512)
                    if (debug >= 1):
                        print('\tSeeking to Cluster (Bytes) [Cluster]: ' + '[' + str(cluster) + ']' + str(seeker))
                    chunk = r.read(ClusterSize)
                    if (debug >= 2):
                        print('\tData Chunk Written: ' + str(chunk))
                    f.write(chunk)
        if (debug >= 1):
            print('\tCompleted Writing Data.')
    except:
        error = 'Error: Cannot Write Data.'
        status = False
    finally:
        return status, error


def PackClusterList(filename, size, clusterlist):
    status = True
    error = ''
    data = ''
    lzc = lzma.LZMACompressor()
    try:
        if (debug >= 1):
            print('Entering PackClusterList:')
        if (debug >= 2):
            print('\tFilename passed in: ' + str(filename))
            print('\tSize passed in: ' + str(size))
            print('\tCluster List passed in [Length]: ' + '[' + str(len(clusterlist)) + '] ' + str(clusterlist))
            #print('\tKey passed in: ' + str(key))
        data += filename
        data += ':'
        data += str(size)
        for cluster in clusterlist:
            data += ':' + str(cluster)
        #f = lzma.compress(bytes(data, encoding='ascii'))
        f = lzc.compress(bytes(data, encoding='ascii'))
        f += lzc.flush()
    except:
        status = False
        error = 'Cannot pack Cluster List.'
    finally:
        if (debug >= 2):
            print('\tPacked list length: ' + str(len(f)))
        return status, error, f


def WriteCompressedClusters(volume, packedlist):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering WriteCompressedClusters')
        if (debug >= 2):
            print('\tVolume passed in: ' + str(volume))
            print('\tPackedlist passed in [Length]: ' + '[' + str(len(packedlist)) + '] - ' + str(packedlist))

        with open(volume, "rb+") as r:
            if (debug >= 1):
                print('\tOpening Volume: ' + str(volume))
                print('\tSeeking to : ' + str(FSInfoSector * BytesPerSector + 4))
            temp1 = 1536
            temp = FSInfoSector * BytesPerSector + 4  #This is the offset tyo FSINFO
            if (debug >= 2):
                print('\tWriting ' + str(len(packedlist)) + ' bytes to offset: ' + str(temp))
            r.seek(temp1)
            r.write(struct.pack("I", len(packedlist)))
            r.write(packedlist)

    except:
        error = 'Error: Cannot Write Cluster List.'
        status = False
    finally:
        return status, error


def WriteCompressedData(volume, filename, clusterlist):
    status = True
    error = ''
    chunk = ''
    try:
        if (debug >= 1):
            print('Entering WriteCompressedData:')
        if (debug >= 2):
            print('\tVolume passed in: ' + str(volume))
            print('\tFilename passed in: ' + str(filename))
            print('\tClusterlist passed in: ' + str(clusterlist))

        with open(volume, "rb+") as f:
            if (debug >= 1):
                print('Opening Volume: ' + str(volume))
            with open(filename, "rb") as r:
                if (debug >= 1):
                    print('\tReading file: ' + str(ntpath.basename(filename)))
                for cluster in clusterlist:  #New Offset is 2 (Cluster)
                    seeker = (cluster * ClusterSize + (DataAreaStart * BytesPerSector) - 2 * ClusterSize)
                    f.seek(seeker)  #Each ClusterNum - 2 (Offset) * Bytes per cluster + (DataAreaStart * 512)
                    if (debug >= 2):
                        print('\tSeeking to Cluster (Bytes) [Cluster]: ' + '[' + str(cluster) + ']' + str(seeker))
                    chunk = r.read(ClusterSize)
                    if (debug >= 2):
                        print('\tData Chunk Written: ' + str(chunk))
                    f.write(chunk)
            if (debug >= 1):
                print('\tCompleted Writing Data.')
    except:
        error = 'Error: Cannot Write Compressed Data.'
        status = False
    finally:
        return status, error


def ReadCompressedClusters(volume):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering ReadCompressedClusters:')
        if (debug >= 2):
            print('\tVolume passed in: ' + str(volume))

        with open(volume, "rb") as r:
            if debug >= 1:
                print('\tOpening Volume: ' + str(volume))
                print('\tSeeking to : ' + str(FSInfoSector * BytesPerSector + 4))
            temp = FSInfoSector * BytesPerSector + 4
            temp1 = 1536
            #if (debug >= 2):

            r.seek(temp1)
            length = struct.unpack("I", r.read(4))[0]  #Get length of LZMA compressed string
            if (debug >= 2):
                print('\tLength of compressed data: ' + str(length))
            r.seek(temp1 + 4)
            lzmadata = r.read(length)
            if (debug >= 3):
                print('\tCompressed data: ' + str(lzmadata))
            data = lzma.decompress(bytes(lzmadata))
            if debug >= 2:
                print('\tUncompressed Data: ' + str(data))
    except:
        error = 'Error: Cannot Read Compressed Cluster List.'
        status = False
    finally:
        return status, error, data


def SearchDirectory(volume, file, write):
    status = True
    error = ''
    global FileName
    try:
        if (debug >= 1):
            print('Entering SearchDirectory:')
        if (debug >= 2):
            print('\tVolume passed in: ' + str(volume))
            print('\tFile passed in: ' + str(file))
            print('\tWrite Flag passed in: ' + str(write))
        s1 = FileName
        if (debug >= 2):
            print('\tFilename to Search: ' + str(s1))
        match = False
        global FirstCluster
        global FileSize
        with open(volume, "rb") as f:
            if (debug >= 2):
                print('\tSeeking to First Data Sector [Bytes]: ' + str(BytesPerSector * FirstDataSector))
            x = 0
            while (True):
                f.seek(BytesPerSector * FirstDataSector + x)
                bytes = f.read(32)  #Size of FAT32 Directory
                FirstChar = struct.unpack("b", bytes[0:1])[0]
                if not (FirstChar == 0x00):  #Check for Unallocated Dir (This means exit!)
                    if not (FirstChar == 0xe5):  #Check for Unallocated Dir
                        filename = bytes[0:11]
                        if (debug >= 3):
                            print('\tFirst Character not 0xe5 or 0x00.')
                            print('\tReading First 11 Bytes.')
                            print('\tDirectory Value: ' + str(filename))
                        if (filename.upper() == s1):
                            match = True
                            if (debug >= 3):
                                print('\tFound Value That Matched: ' + str(s1))
                            if not (write):
                                ba = bytearray(bytes[26:28])
                                ba += bytes[20:22]
                                if (debug >= 2):
                                    print('\tHigh/Low Bytes Bytearray [Length]: ' + '[' + str(len(ba)) + ']' + str(ba))
                                FirstCluster = struct.unpack("<i", ba)[0]
                                if (debug >= 1):
                                    print('\tFirst Cluster: ' + str(FirstCluster))
                                ba1 = bytearray(bytes[28:32])
                                FileSize = struct.unpack("<i", ba1)[0]
                                if (debug >= 2):
                                    print('\tFilesize Located in Directory [Bytes]: ' + str(FileSize))
                            else:
                                return match
                            break
                        else:
                            x += 32
                    else:
                        break
                else:
                    break
    except:
        error = 'Error Searching Directory.'
        status = False
    finally:
        return match


def UnpackClusterList(volume, data):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering UnpackClusterList:')
        if (debug >= 2):
            print('\tVolume passed in: ' + str(volume))
            print('\tData passed in: ' + str(data))

        data = data.decode(encoding='ascii')
        decodeddata = data.split(':')
        filename = decodeddata.pop(0)  #Pop off the filename
        filesize = decodeddata.pop(0)  #Pop off the filesize
        if (debug >= 2):
            print('\tFilename: ' + str(filename))
            print('\tFile size: ' + str(filesize))
            print('\tDecoded clusterlist: ' + str(decodeddata))
    except:
        error = 'Error: Cannot Read Compressed Cluster List.'
        status = False
    finally:
        return status, error, filename, filesize, decodeddata


def SearchFAT(volume, FATOffset, FirstCluster):
    status = True
    error = ''
    global ReadClusterList

    try:
        if (debug >= 1):
            print('Entering SearchFAT:')
            print('\tFirstCluster passed in: ' + str(FirstCluster))
            print('\tVolume passed in: ' + str(volume))

        nextcluster = FirstCluster
        ReadClusterList.append(nextcluster)
        y = 0
        with open(volume, "rb") as f:
            f.seek(FATOffset * BytesPerSector)
            bytes = f.read(TotalFAT32Bytes)
            if (debug >= 2):
                print('\tSeeking to FAT Offset (Bytes): ' + str(FATOffset * BytesPerSector))
            while (y <= TotalFAT32Bytes):
                y += 4
                chunk = bytes[nextcluster * 4:nextcluster * 4 + 4]
                nextcluster = struct.unpack("<i", chunk)[0]
                if (debug >= 3):
                    print('\tCluster Read [Length]: ' + '[' + str(len(chunk)) + ']' + str(chunk))
                if (debug >= 2):
                    print('\tNext Cluster: ' + str(nextcluster))
                if (nextcluster != 268435455):
                    ReadClusterList.append(nextcluster)
                else:
                    break
        if (debug >= 2):
            print('\tCluster List: ' + str(ReadClusterList))
            #return ReadClusterList
    except:
        error = 'Error: Cannot Search FAT.'
        status = False
    finally:
        return status, error


def ReadData(volume, clusterlist, size):
    status = True
    error = ''
    filedata = ''
    try:
        if (debug >= 1):
            print('Entering ReadData:')
        if (debug >= 2):
            print('Volume Passed in: ' + str(volume))
            print('Clusterlist Passed in: ' + str(clusterlist))
            print('Size in: ' + str(size))
        readchunk = bytearray()
        with open(volume, "rb") as f:
            for cluster in clusterlist:  #New Offset is 2 (Cluster)
                seeker = (int(cluster) * ClusterSize + (DataAreaStart * BytesPerSector) - 2 * ClusterSize)
                f.seek(seeker)  #Each ClusterNum - 2 (Offset) * Bytes per cluster + (DataAreaStart * BytesPerSector)
                if (debug >= 2):
                    print('\tSeeking to Cluster (Bytes) [Cluster]: ' + '[' + str(cluster) + ']' + str(seeker))
                readchunk += f.read(ClusterSize)
            filedata = readchunk[0:int(size)]
            if (debug >= 3):
                print('\tFile Data: ' + str(FileData))
    except:
        error = ('Error: Cannot Read Data.')
        status = False
    finally:
        return status, error, filedata


def WriteDatatoFile(file, filedata):
    status = True
    error = ''
    global FileData
    global MD5HashValue
    try:
        if (debug >= 1):
            print('Entering WriteDatatoFile:')
        if not (FileData == ''):
            with open(file, "wb") as f:
                f.write(FileData)
            md5 = hashlib.md5()
            md5.update(FileData)
            MD5HashValue = md5.hexdigest()
        else:
            error = 'File Data is Emtpy.'
    except:
        error = 'Error: Cannot Write Data.'
        status = False
    finally:
        return status, error


def WriteFSInfo(volume):
    status = True
    error = ''

    try:
        if (debug >= 1):
            print('Entering WriteFSInfo:')
        #Number of Free Clusters - 488-491
        #Next Free Cluster 492-495
        global NumberOfFreeClusters
        global NextFreeCluster

        with open(volume, "rb+") as f:
            f.seek(FSInfoSector * BytesPerSector + 488)
            f.write(struct.pack("i", NumberOfFreeClusters))
            if (debug >= 2):
                print('Number of Free Clusters: ' + str(NumberOfFreeClusters))
            f.seek(FSInfoSector * BytesPerSector + 492)
            f.write(struct.pack("i", NextFreeCluster))
            if (debug >= 2):
                print('Next Free Cluster: ' + str(NextFreeCluster))
    except:
        error = 'Error: Cannot Write FSInfo.'
        status = True
    finally:
        return status, error


def signal_handler(signal, frame):
    print('Ctrl+C pressed. Exiting.')
    sys.exit(0)


def Header():
    print('')
    print('+---------------------------------------------------------------------------+')
    print('|FAT32 File Bad Cluster Utility                                             |')
    print('+----------------------------------------------------------------------------')
    print('|Author: Tahir Khan - tkhan9@gmu.edu                                        |')
    print('+---------------------------------------------------------------------------+')
    print('  Date Run: ' + str(datetime.datetime.now()))
    print('+---------------------------------------------------------------------------+')


def Failed(error):
    print('  * Error: ' + str(error))
    print('+---------------------------------------------------------------------------+')
    print('|  [*] Failed.                                                              |')
    print('+---------------------------------------------------------------------------+')
    sys.exit(1)


def Completed(file):
    print('|  [*] Completed.                                                           |')
    print('+---------------------------------------------------------------------------+')
    print('  File: ' + str(ntpath.basename(file)) + ' - ' + 'MD5: ' + str(MD5HashValue))
    print('+---------------------------------------------------------------------------+')
    sys.exit(0)


def CompletedFrag(file):
    print('| Completed.                                                                |')
    print('+---------------------------------------------------------------------------+')
    print('  File: ' + str(ntpath.basename(file)) + ' - ' + 'MD5: ' + str(MD5HashValue))
    print('  --> Start Cluster:    ' + str(FirstCluster))
    print('  --> End Cluster:      ' + str(ChunkList[-1]))
    print('  --> Skipped Clusters: ' + str(SkippedClusters))
    print('+---------------------------------------------------------------------------+')
    sys.exit(0)


signal.signal(signal.SIGINT, signal_handler)


def main(argv):
    status = True
    read = False
    global debug
    global MD5HashValue
    parser = argparse.ArgumentParser(description="A FAT32 file system writer that hides data in bad clusters.",
                                     add_help=True)
    parser.add_argument('-f', '--file', help='The filename to write to the FAT32 volume or the filename to output.',
                        required=True)
    parser.add_argument('-v', '--volume', help='The volume to write the file to.', required=True)
    parser.add_argument('-d', '--debug', help='The level of debugging.', required=False)
    rwgroup = parser.add_mutually_exclusive_group()
    rwgroup.add_argument('-w', '--write', help='Write a file to the FAT32 volume.', action='store_true',
                         required=False)
    rwgroup.add_argument('-r', '--read', help='Read a file from the FAT32 volume.', action='store_true',
                         required=False)
    parser.add_argument('--version', action='version', version='%(prog)s 1.5')
    args = parser.parse_args()
    if (args.file):
        file = args.file
        with open(file):
            status = True
            MD5HashValue = HashMD5(file)
    if (args.volume):
        volume = args.volume
    if (args.read):
        read = args.read
    if (args.debug):
        debug = args.debug
        debug = int(debug)
    if _platform == "linux" or _platform == "linux2":
        ostype = 'Linux'
    elif _platform == "darwin":
        ostype = 'Mac'
    elif _platform == "win32":
        ostype = 'Windows'
    if (debug >= 1):
        print('Entered main:')
        print('\tFilename to Hide: ' + str(file))
        print('File Input: ' + str(ntpath.basename(file)) + ' - ' + 'MD5: ' + str(MD5HashValue))
        print('\tVolume: ' + str(volume))
        print('\tOperating System: ' + str(os))
        print('\tDebug Level: ' + str(debug))
    Header()
    status, error = ReadBootSector(volume)
    if (status):
        print('|  [+] Reading Boot Sector.                                                 |')
    else:
        print('|  [-] Reading Boot Sector.                                                 |')
        Failed(error)
    status, error = GetFSInfo(volume)
    if (status):
        print('|  [+] Reading FSInfo.                                                      |')
    else:
        print('|  [-] Reading FSInfo.                                                      |')
        Failed(error)

    if not read:
        status, error = GetChunks(file)
        if (status):
            print('|  [+] Calculating Clusters.                                                |')
        else:
            print('|  [-] Calculating Clusters.                                                |')
            Failed(error)
        status, error = ReadFat(volume, TotalChunks)
        if (status):
            print('|  [+] Reading FAT.                                                         |')
        else:
            print('|  [-] Reading FAT.                                                         |')
            Failed(error)
        status, error = WriteFAT(volume, ChunkList)
        if (status):
            print('|  [+] Marking FAT with Bad Clusters.                                       |')
        else:
            print('|  [-] Marking FAT with Bad Clusters.                                       |')
            Failed(error)
        status, error, packedlist = PackClusterList(ntpath.basename(file), os.path.getsize(file), ChunkList)
        if (status):
            print('|  [+] Packing Actual Cluster List.                                         |')
        else:
            print('|  [-] Packing Actual Cluster List.                                         |')
            Failed(error)
        status, error = WriteCompressedClusters(volume, packedlist)
        if (status):
            print('|  [+] Writing Compressed Cluster List.                                     |')
        else:
            print('|  [-] Writing Compressed Cluster List.                                     |')
            Failed(error)
        status, error = WriteCompressedData(volume, file, ChunkList)
        if (status):
            print('|  [+] Writing Compressed Data.                                             |')
        else:
            print('|  [-] Writing Compressed Data.                                             |')
            Failed(error)
        status, error = GetNextFreeCluster(volume)
        if (status):
            print('|  [+] Getting Next Free Cluster.                                           |')
        else:
            print('|  [-] Getting Next Free Cluster.                                           |')
            Failed(error)
        status, error = WriteFSInfo(volume)
        if (status):
            print('|  [+] Updating FSInfo.                                                     |')
        else:
            print('|  [-] Updating FSInfo.                                                     |')
            Failed(error)
    else:
        status, error, data = ReadCompressedClusters(volume)
        if (status):
            print('|  [+] Reading Compressed Cluster List.                                     |')
        else:
            print('|  [-] Reading Compressed Cluster List.                                     |')
            Failed(error)
        status, error, filename, filesize, decodeddata = UnpackClusterList(volume, data)
        if (status):
            print('|  [+] Unpacking Cluster List.                                              |')
        else:
            print('|  [-] Unpacking Cluster List.                                              |')
            Failed(error)
        status, error, filedata = ReadData(volume, decodeddata, filesize)
        if (status):
            print('|  [+] Reading Data.                                                        |')
        else:
            print('|  [-] Reading Data.                                                        |')
            Failed(error)
        status, error = WriteDatatoFile(file, filedata)
        if (status):
            print('|  [+] Writing Data.                                                        |')
        else:
            print('|  [-] Writing Data.                                                        |')
            Failed(error)
    #except IOError:
    #    sys.exit('Error: File ' + str(file) + ' does not exist.')
    Completed(file)


main(sys.argv[1:])