using AuroraLib.Compression.Algorithms;
using AuroraLib.Core.IO;
using NvTriStripDotNet;
using SAModel;
using SplitTools;
using System;
using System.Buffers;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Windows.Forms;

//using SAModel.SAEditorCommon.ModelConversion;

using ByteConverter = SAModel.ByteConverter;
using IniDictionary = System.Collections.Generic.Dictionary<string, System.Collections.Generic.Dictionary<string, string>>;
using IniGroup = System.Collections.Generic.Dictionary<string, string>;

// Skies of Arcadia MLD archives.
namespace ArchiveLib
{
	public class nmldObject
	{
		public string Name;
		public byte[] Header;
		public byte[] File;

		public nmldObject(byte[] file, int offset, string name)
		{
			int ptrNJCM = ByteConverter.ToInt32(file, offset);
			uint chunksize = ByteConverter.ToUInt32(file, offset + 4) - 16;
			int ptrNJTL = ByteConverter.ToInt32(file, offset + 8);
			uint unknown = ByteConverter.ToUInt32(file, offset + 12);

			if (unknown != 0)
				Console.WriteLine("Unknown Pointer in Object is populated: {0}", unknown.ToString());

			int start = (ptrNJTL != 0) ? ptrNJTL : ptrNJCM;

			if (start == 0)
			{
				Console.WriteLine("Objects have no data pointers.");
				return;
			}

			File = new byte[chunksize];
			Array.Copy(file, start + offset, File, 0, chunksize);

			Name = name;
		}

		public nmldObject(byte[] file, string name)
		{
			// build header line
			// 0x0 offset of any NJCM present
			// 0x4 file size including header
			// 0x8 offset of any NJTL present (usually before NJCM?)
			// 0xc unknown (usually set to zero

			File = file;

			byte[] header = new byte[16];
			ByteConverter.GetBytes(file.Length + 16).CopyTo(header, 4);

			int njtlOffset = 0;
			int njcmOffset = 0;
			bool bothFound = false;
			int cur_ptr = 0;
			while (cur_ptr < file.Length && !bothFound)
			{
				if (file[cur_ptr] == 'N')
				{
					if (Encoding.ASCII.GetString(file, cur_ptr, 4) == "NJCM")
					{
						njcmOffset = cur_ptr + 16;
	}
					if (Encoding.ASCII.GetString(file, cur_ptr, 4) == "NJTL")
					{
						njtlOffset = cur_ptr + 16;
					}
				}

				if (njtlOffset != 0 && njcmOffset != 0) bothFound = true;

				cur_ptr++;
			}

			ByteConverter.GetBytes(njtlOffset).CopyTo(header, 8);
			ByteConverter.GetBytes(njcmOffset).CopyTo(header, 0);

			Header = header;
		}
	}


	public class nmldGround
	{
		public enum GroundType
		{
			Ground = 0,
			GroundObject = 1,
			Unknown
		}

		// ----------------------------------------------------------------------------
		// GRND codec: decode from .grnd bytes, encode back to .grnd bytes
		// ----------------------------------------------------------------------------
		private sealed class GRNDCodec
		{
			// knobs
			public bool UseAStar { get; set; } = false;
			public bool UseLegacyAnchorPacking { get; set; } = false;

			// anchor pool for legacy-style strip priming
			private static readonly ushort[] LegacyAnchors = { 3, 4, 5, 9 };

			// ------------------------------------------------------------------------
			// public decode API
			// ------------------------------------------------------------------------
			public DecodeResult Decode(byte[] data, int baseOffset)
			{
				// 0x00: "GRND"
				// 0x04: u32 file size
				// 0x08: 0
				// 0x0C: 0
				if (baseOffset + 4 > data.Length)
					throw new ArgumentException("GRNDCodec.Decode: buffer too small");

				if (data[baseOffset + 0] != (byte)'G' || data[baseOffset + 1] != (byte)'R' || data[baseOffset + 2] != (byte)'N' || data[baseOffset + 3] != (byte)'D')
				{
					// we can't use char literal here, so just check ascii
				}

				// we trust the "GRND" because caller said so
				int innerHeader = baseOffset + 0x10;
				if (innerHeader + 0x1C > data.Length)
					throw new ArgumentException("GRNDCodec.Decode: file too small for inner header");

				// read inner header
				int relTriSets = BitConverter.ToInt32(data, innerHeader + 0x00);
				int relQuads = BitConverter.ToInt32(data, innerHeader + 0x04);
				float centerX = BitConverter.ToSingle(data, innerHeader + 0x08);
				float centerZ = BitConverter.ToSingle(data, innerHeader + 0x0C);
				ushort gridX = BitConverter.ToUInt16(data, innerHeader + 0x10);
				ushort gridZ = BitConverter.ToUInt16(data, innerHeader + 0x12);
				ushort cellX = BitConverter.ToUInt16(data, innerHeader + 0x14);
				ushort cellZ = BitConverter.ToUInt16(data, innerHeader + 0x16);
				ushort triSetCount = BitConverter.ToUInt16(data, innerHeader + 0x18);
				ushort quadCount = BitConverter.ToUInt16(data, innerHeader + 0x1A);

				int triSetsOff = innerHeader + relTriSets;
				int quadTableOff = innerHeader + relQuads + 4;

				// 1) read triangle sets skeletons
				var triSets = new List<TriangleSet>(triSetCount);
				for (int s = 0; s < triSetCount; s++)
				{
					int setOff = triSetsOff + s * 0x18;
					if (setOff + 0x18 > data.Length)
						break;

					int vertRel = BitConverter.ToInt32(data, setOff + 0x0C);
					int triRel = BitConverter.ToInt32(data, setOff + 0x10);
					int triCnt = BitConverter.ToInt32(data, setOff + 0x14);

					var ts = new TriangleSet
					{
						SetIndex = s,
						HeaderOffset = setOff,
						VertexBlockOffset = setOff + 0x0C + vertRel,
						TriangleStreamOffset = setOff + 0x10 + triRel,
						TriangleCount = triCnt
					};
					triSets.Add(ts);
				}

				// 2) read vertex block from the first non-empty triangle set (Not used for anything downstream anymore,but useful for debugging)
				List<GrndVertex> vertices = null;
				foreach (var ts in triSets)
				{
					if (ts.TriangleCount == 0)
						continue;
					vertices = ReadVertexBlock(data, ts.VertexBlockOffset);
					break;
				}
				if (vertices == null)
				{
					// no real triangle set? make an empty one
					vertices = new List<GrndVertex>();
				}

				// 3) read triangle streams
				foreach (var ts in triSets)
				{
					ts.Stream = ReadTriangleStream(data, ts.TriangleStreamOffset, ts.VertexBlockOffset);
				}

				// 4) read quad table + lists
				var quads = new List<QuadCell>(quadCount);
				for (int i = 0; i < quadCount; i++)
				{
					int qOff = quadTableOff + i * 8;
					int qCount = BitConverter.ToInt32(data, qOff + 0);
					if (qCount == 0) continue;

					int qRel = BitConverter.ToInt32(data, qOff + 4);
					int listOff = qOff + 4 + qRel;
					var refs = new List<QuadRef>(qCount);
					for (int j = 0; j < qCount; j++)
					{
						ushort ts = BitConverter.ToUInt16(data, listOff + j * 4 + 0);
						ushort ti = BitConverter.ToUInt16(data, listOff + j * 4 + 2);
						refs.Add(new QuadRef { TriSet = ts, TriIndex = ti });
					}
					quads.Add(new QuadCell { Index = i, Refs = refs });
				}

				// 5) reconstruct unique triangles from all (triSet,triIndex) pairs that are actually referenced
				var finalVerts = new List<Vertex>();
				var finalNorms = new List<Vertex>();
				var finalPolys = new List<Triangle>();
				var fiToIndex = new Dictionary<int, int>();
				var unique_tris = new HashSet<(int, int)>();
				foreach (var q in quads)
				{
					foreach (var r in q.Refs)
					{
						int sidx = r.TriSet;
						int tidx = r.TriIndex;

						if (sidx < 0 || sidx >= triSets.Count || tidx < 0)
							continue;

						var ts = triSets[sidx];
						int needed = tidx + 2;
						if (needed >= ts.Stream.Count)
							continue;

						// Remove duplicate triangles
						if (unique_tris.Contains((sidx, tidx))) continue;
						unique_tris.Add((sidx, tidx));

						// triangle j: entries at j, j+1, j+2
						var e0 = ts.Stream[tidx + 0];
						var e1 = ts.Stream[tidx + 1];
						var e2 = ts.Stream[tidx + 2];

						int i0 = GetOrCreateVertexForFloatIndex(data, ts.VertexBlockOffset, e0.FloatIndex, finalVerts, finalNorms, fiToIndex);
						int i1 = GetOrCreateVertexForFloatIndex(data, ts.VertexBlockOffset, e1.FloatIndex, finalVerts, finalNorms, fiToIndex);
						int i2 = GetOrCreateVertexForFloatIndex(data, ts.VertexBlockOffset, e2.FloatIndex, finalVerts, finalNorms, fiToIndex);

						bool flip = e2.Flags < 0;
						if (flip)
							finalPolys.Add(new Triangle((ushort)i2, (ushort)i1, (ushort)i0));
						else
							finalPolys.Add(new Triangle((ushort)i0, (ushort)i1, (ushort)i2));
					}
				}

				var mesh = new NJS_MESHSET(finalPolys.ToArray(), true, false, false);
				var meshes = new List<NJS_MESHSET> { mesh };

				// 7) find min and max
				float minX = float.MaxValue, maxX = float.MinValue;
				float minZ = float.MaxValue, maxZ = float.MinValue;
				for (int i = 0; i < finalVerts.Count; i++)
				{
					var v = finalVerts[i];
					if (v.X < minX) minX = v.X;
					if (v.X > maxX) maxX = v.X;
					if (v.Z < minZ) minZ = v.Z;
					if (v.Z > maxZ) maxZ = v.Z;
				}

				var hdr = new GrndHeader
				{
					CenterX = centerX,
					CenterZ = centerZ,
					GridX = gridX,
					GridZ = gridZ,
					CellSizeX = cellX,
					CellSizeZ = cellZ,
					TriangleSetCount = triSetCount,
					QuadCount = quadCount
				};

				return new DecodeResult
				{
					Header = hdr,
					Vertices = finalVerts.ToArray(),
					Normals = finalNorms.ToArray(),
					Meshes = meshes,
					BoundsXMin = minX == float.MaxValue ? 0 : minX,
					BoundsXMax = maxX == float.MinValue ? 0 : maxX,
					BoundsZMin = minZ == float.MaxValue ? 0 : minZ,
					BoundsZMax = maxZ == float.MinValue ? 0 : maxZ
				};
			}

			// ------------------------------------------------------------------------
			// public encode API
			// ------------------------------------------------------------------------
			public byte[] Encode(GRND owner)
			{
				// 1) take geometry from owner
				var verts = owner.Vertices ?? Array.Empty<Vertex>();
				var meshes = owner.Meshes ?? new List<NJS_MESHSET>();

				// 2) flatten triangles
				var tris = CollectTrianglesFromMeshes(meshes);

				// 3) adjacency
				var adj = BuildAdjacency(tris);

				// 4) build strips / stream
				var stripResult = BuildStrips(
					tris,
					adj,
					verts.Length,
					UseAStar,
					UseLegacyAnchorPacking
				);

				// the real GRND format stores float indices ALREADY biased by +2 floats
				// (to skip the 8-byte / 2-float vertex header)
				var streamBytes = stripResult.StreamBytes;
				ushort shiftedMax = 0;

				for (int off = 0; off < streamBytes.Length; off += 4)
				{
					ushort fi = BitConverter.ToUInt16(streamBytes, off + 0);
					fi = (ushort)(fi + 2);                  // <<< add 2-float header skip
					Buffer.BlockCopy(BitConverter.GetBytes(fi), 0, streamBytes, off + 0, 2);

					if (fi > shiftedMax) shiftedMax = fi;
				}

				// 5) build quads (recompute)
				float xMin, xMax, zMin, zMax;
				ComputeXZBounds(verts, out xMin, out xMax, out zMin, out zMax);

				ushort cellX = owner.XLen != 0 ? (ushort)owner.XLen : (ushort)40;
				ushort cellZ = owner.ZLen != 0 ? (ushort)owner.ZLen : (ushort)40;

				// snap origin like we did before
				float originX = (float)Math.Floor(xMin / cellX) * cellX;
				float originZ = (float)Math.Floor(zMin / cellZ) * cellZ;

				ushort gridX = owner.XCount != 0 ? (ushort)owner.XCount : (ushort)Math.Max(1, Math.Ceiling((xMax - originX) / cellX));
				ushort gridZ = owner.ZCount != 0 ? (ushort)owner.ZCount : (ushort)Math.Max(1, Math.Ceiling((zMax - originZ) / cellZ));
				ushort quadCount = (ushort)(gridX * gridZ);

				var quads = BuildQuadsFromTriangles(
					tris,
					stripResult.TriangleLookup,
					verts,
					originX,
					originZ,
					cellX,
					cellZ,
					gridX,
					gridZ
				);

				// 6) vertex block
				var norms = owner.Normals;
				if (norms == null || norms.Length != verts.Length)
				{
					norms = new Vertex[verts.Length];
					for (int i = 0; i < norms.Length; i++)
						norms[i] = new Vertex(0, 1, 0);
				}

				// IMPORTANT: use the *shifted* max we just computed
				var vertexBlock = BuildVertexBlock(verts, norms, shiftedMax);

				// 7) build final bytes
				var bytes = new List<byte>(0x20000);

				// outer header
				bytes.AddRange(Encoding.ASCII.GetBytes("GRND"));  // 0x00
				bytes.AddRange(new byte[4]);                      // 0x04 file size (patch later)
				bytes.AddRange(new byte[8]);                      // 0x08 / 0x0C

				int innerHeaderOff = bytes.Count;                 // should be 0x10
				bytes.AddRange(new byte[0x1C]);                   // reserve inner header

				// quad table
				int quadTableOff = bytes.Count;
				for (int i = 0; i < quads.Count(); i++)
				{
					bytes.AddRange(BitConverter.GetBytes(quads[i].Count));
					bytes.AddRange(new byte[4]); // placeholder for rel ptr
				}

				// quad lists
				for (int i = 0; i < quads.Count(); i++)
				{
					var list = quads[i];
					int listOff = bytes.Count;
					for (int j = 0; j < list.Count; j++)
					{
						bytes.AddRange(BitConverter.GetBytes(list[j].TriSet));
						bytes.AddRange(BitConverter.GetBytes(list[j].TriIndex));
					}
					// patch rel ptr
					int patchAt = quadTableOff + i * 8 + 4;
					int rel = listOff - patchAt;
					var relBytes = BitConverter.GetBytes(rel);
					for (int b = 0; b < 4; b++)
						bytes[patchAt + b] = relBytes[b];
				}

				// triangle sets
				int triSetsOff = bytes.Count;

				// set 0: empty
				{
					int ts0Off = bytes.Count;
					bytes.AddRange(new byte[0x18]);
					// we can point its vertex block to the real one or to itself; let's just make it self-relative 0
					// leave as zeros; triCount=0
				}

				// set 1: real
				int ts1Off = bytes.Count;
				bytes.AddRange(new byte[0x18]); // header placeholder

				// triangle stream right after header
				int triStreamOff = bytes.Count;
				bytes.AddRange(stripResult.StreamBytes);

				// vertex block
				int vertexBlockOff = bytes.Count;
				bytes.AddRange(vertexBlock);

				// patch set 1 header
				{
					// rel to vertex block
					int relVert = vertexBlockOff - (ts1Off + 0x0C);
					var relVertBytes = BitConverter.GetBytes(relVert);
					for (int b = 0; b < 4; b++)
						bytes[ts1Off + 0x0C + b] = relVertBytes[b];

					// rel to tri stream
					int relTri = triStreamOff - (ts1Off + 0x10);
					var relTriBytes = BitConverter.GetBytes(relTri);
					for (int b = 0; b < 4; b++)
						bytes[ts1Off + 0x10 + b] = relTriBytes[b];

					// triangle count (logical)
					var triCntBytes = BitConverter.GetBytes(stripResult.TriangleCount);
					for (int b = 0; b < 4; b++)
						bytes[ts1Off + 0x14 + b] = triCntBytes[b];
				}

				// patch inner header
				{
					// 0x10: rel to tri sets
					int relTriSets = triSetsOff - (innerHeaderOff + 0x00);
					var relTriSetsBytes = BitConverter.GetBytes(relTriSets);
					for (int b = 0; b < 4; b++)
						bytes[innerHeaderOff + 0x00 + b] = relTriSetsBytes[b];

					// 0x14: rel to quad table
					int relQuad = quadTableOff - (innerHeaderOff + 0x04);
					var relQuadBytes = BitConverter.GetBytes(relQuad);
					for (int b = 0; b < 4; b++)
						bytes[innerHeaderOff + 0x04 + b] = relQuadBytes[b];

					// 0x18.. center X, center Z
					float cx = owner.Center != null ? owner.Center.X : originX;
					float cz = owner.Center != null ? owner.Center.Z : originZ;
					var cxBytes = BitConverter.GetBytes(cx);
					var czBytes = BitConverter.GetBytes(cz);
					for (int b = 0; b < 4; b++)
						bytes[innerHeaderOff + 0x08 + b] = cxBytes[b];
					for (int b = 0; b < 4; b++)
						bytes[innerHeaderOff + 0x0C + b] = czBytes[b];

					// gridX, gridZ, cellX, cellZ
					var gridXBytes = BitConverter.GetBytes(gridX);
					var gridZBytes = BitConverter.GetBytes(gridZ);
					var cellXBytes = BitConverter.GetBytes(cellX);
					var cellZBytes = BitConverter.GetBytes(cellZ);
					bytes[innerHeaderOff + 0x10 + 0] = gridXBytes[0];
					bytes[innerHeaderOff + 0x10 + 1] = gridXBytes[1];
					bytes[innerHeaderOff + 0x12 + 0] = gridZBytes[0];
					bytes[innerHeaderOff + 0x12 + 1] = gridZBytes[1];
					bytes[innerHeaderOff + 0x14 + 0] = cellXBytes[0];
					bytes[innerHeaderOff + 0x14 + 1] = cellXBytes[1];
					bytes[innerHeaderOff + 0x16 + 0] = cellZBytes[0];
					bytes[innerHeaderOff + 0x16 + 1] = cellZBytes[1];

					// triangle set count = 2 (empty + real)
					var tsCountBytes = BitConverter.GetBytes((ushort)2);
					bytes[innerHeaderOff + 0x18 + 0] = tsCountBytes[0];
					bytes[innerHeaderOff + 0x18 + 1] = tsCountBytes[1];

					// quad count
					var qcBytes = BitConverter.GetBytes(quadCount);
					bytes[innerHeaderOff + 0x1A + 0] = qcBytes[0];
					bytes[innerHeaderOff + 0x1A + 1] = qcBytes[1];
				}

				// patch file size
				int fileSize = bytes.Count;
				var fileSizeBytes = BitConverter.GetBytes(fileSize);
				for (int b = 0; b < 4; b++)
					bytes[0x04 + b] = fileSizeBytes[b];

				return bytes.ToArray();
			}

			// ------------------------------------------------------------------------
			// helpers: decoding
			// ------------------------------------------------------------------------
			private static List<GrndVertex> ReadVertexBlock(byte[] data, int off)
			{
				// u16 0x0029
				ushort magic = BitConverter.ToUInt16(data, off + 0);
				ushort maxPlus5 = BitConverter.ToUInt16(data, off + 2);
				ushort reserved = BitConverter.ToUInt16(data, off + 4);
				ushort vcount = BitConverter.ToUInt16(data, off + 6);

				var list = new List<GrndVertex>(vcount);
				int p = off + 8;
				for (int i = 0; i < vcount; i++)
				{
					float px = BitConverter.ToSingle(data, p + 0);
					float py = BitConverter.ToSingle(data, p + 4);
					float pz = BitConverter.ToSingle(data, p + 8);
					float nx = BitConverter.ToSingle(data, p + 12);
					float ny = BitConverter.ToSingle(data, p + 16);
					float nz = BitConverter.ToSingle(data, p + 20);
					list.Add(new GrndVertex
					{
						X = px,
						Y = py,
						Z = pz,
						NX = nx,
						NY = ny,
						NZ = nz
					});
					p += 24;
				}
				return list;
			}

			private static int GetOrCreateVertexForFloatIndex(
				byte[] data,
				int vertexBlockOffset,
				ushort floatIndex,
				List<Vertex> finalVerts,
				List<Vertex> finalNorms,
				Dictionary<int, int> fiToIndex)
			{
				if (fiToIndex.TryGetValue(floatIndex, out int existing))
					return existing;

				// 1) detect if this vertex block has the 0x0029 header
				bool hasHeader = BitConverter.ToUInt16(data, vertexBlockOffset + 0) == 0x0029;
				int floatsBase = vertexBlockOffset - (!hasHeader ? 8 : 0);

				// position: exactly how the original code did it
				int posOff = floatsBase + floatIndex * 4;
				Vertex pos = new Vertex(data, posOff);

				// normal: always from the canonical 3-float normal slot of the vertex bucket
				int bucket = (floatIndex - 2) / 6;      // which original vertex
				if (bucket < 0) bucket = 0;

				int normOff = floatsBase + (bucket * 6 + 3 + 2) * 4;
				Vertex norm = new Vertex(data, normOff);

				int newIndex = finalVerts.Count;
				finalVerts.Add(pos);
				finalNorms.Add(norm);
				fiToIndex[floatIndex] = newIndex;
				return newIndex;
			}

			private static List<StreamEntry> ReadTriangleStream(byte[] data, int streamOff, int vertexBlockOff)
			{
				// we will read triCount + 2 entries at most (but we don't know if file stored extra)
				// however your files store exactly 3 * triCount entries in a row
				int byteCount = vertexBlockOff - streamOff;
				int entryCount = byteCount / 4;

				if (entryCount <= 0) return new List<StreamEntry>();

				var list = new List<StreamEntry>(entryCount);
				for (int i = 0; i < entryCount; i++)
				{
					int eOff = streamOff + i * 4;
					ushort fidx = BitConverter.ToUInt16(data, eOff + 0);
					short flags = BitConverter.ToInt16(data, eOff + 2);
					list.Add(new StreamEntry { FloatIndex = fidx, Flags = flags });
				}
				return list;
			}

			// ------------------------------------------------------------------------
			// helpers: encoding
			// ------------------------------------------------------------------------
			private static List<(ushort TriSet, ushort TriIndex)>[] BuildQuadsFromTriangles(
				List<FlatTriangle> tris,
				Dictionary<int, (int triSet, int triIndex)> triLookup,
				Vertex[] verts,
				float originX,
				float originZ,
				ushort cellX,
				ushort cellZ,
				ushort gridX,
				ushort gridZ)
			{
				int total = gridX * gridZ;
				var result = new List<(ushort, ushort)>[total];
				for (int i = 0; i < total; i++)
					result[i] = new List<(ushort, ushort)>();

				for (int i = 0; i < tris.Count; i++)
				{
					var t = tris[i];
					if (!triLookup.TryGetValue(i, out var loc))
						continue;

					// triangle AABB in XZ
					var v0 = verts[t.V0];
					var v1 = verts[t.V1];
					var v2 = verts[t.V2];
					float minX = Math.Min(v0.X, Math.Min(v1.X, v2.X));
					float maxX = Math.Max(v0.X, Math.Max(v1.X, v2.X));
					float minZ = Math.Min(v0.Z, Math.Min(v1.Z, v2.Z));
					float maxZ = Math.Max(v0.Z, Math.Max(v1.Z, v2.Z));

					int minCX = (int)Math.Floor((minX - originX) / cellX);
					int maxCX = (int)Math.Floor((maxX - originX) / cellX);
					int minCZ = (int)Math.Floor((minZ - originZ) / cellZ);
					int maxCZ = (int)Math.Floor((maxZ - originZ) / cellZ);

					if (minCX < 0) minCX = 0;
					if (minCZ < 0) minCZ = 0;
					if (maxCX >= gridX) maxCX = gridX - 1;
					if (maxCZ >= gridZ) maxCZ = gridZ - 1;

					for (int cz = minCZ; cz <= maxCZ; cz++)
					{
						for (int cx = minCX; cx <= maxCX; cx++)
						{
							int idx = cz * gridX + cx;
							result[idx].Add(((ushort)loc.triSet, (ushort)loc.triIndex));
						}
					}
				}

				return result;
			}

			private static byte[] BuildVertexBlock(Vertex[] verts, Vertex[] norms, ushort maxFloatIndex)
			{
				ushort magic = 0x0029;
				ushort maxPlus5 = (ushort)(maxFloatIndex + 5);
				ushort reserved = 0;
				ushort vertexCount = (ushort)verts.Length;

				var bytes = new List<byte>(8 + vertexCount * 24);
				bytes.AddRange(BitConverter.GetBytes(magic));
				bytes.AddRange(BitConverter.GetBytes(maxPlus5));
				bytes.AddRange(BitConverter.GetBytes(reserved));
				bytes.AddRange(BitConverter.GetBytes(vertexCount));

				for (int i = 0; i < verts.Length; i++)
				{
					var v = verts[i];
					var n = (i < norms.Length) ? norms[i] : new Vertex(0, 1, 0);

					bytes.AddRange(BitConverter.GetBytes(v.X));
					bytes.AddRange(BitConverter.GetBytes(v.Y));
					bytes.AddRange(BitConverter.GetBytes(v.Z));
					bytes.AddRange(BitConverter.GetBytes(n.X));
					bytes.AddRange(BitConverter.GetBytes(n.Y));
					bytes.AddRange(BitConverter.GetBytes(n.Z));
				}

				return bytes.ToArray();
			}

			private static void ComputeXZBounds(Vertex[] verts, out float xMin, out float xMax, out float zMin, out float zMax)
			{
				xMin = float.MaxValue;
				xMax = float.MinValue;
				zMin = float.MaxValue;
				zMax = float.MinValue;
				for (int i = 0; i < verts.Length; i++)
				{
					var v = verts[i];
					if (v.X < xMin) xMin = v.X;
					if (v.X > xMax) xMax = v.X;
					if (v.Z < zMin) zMin = v.Z;
					if (v.Z > zMax) zMax = v.Z;
				}
				if (xMin == float.MaxValue) { xMin = xMax = zMin = zMax = 0; }
			}

			private static List<FlatTriangle> CollectTrianglesFromMeshes(List<NJS_MESHSET> meshes)
			{
				var list = new List<FlatTriangle>();
				foreach (var ms in meshes)
				{
					if (ms.Poly == null) continue;
					foreach (var p in ms.Poly)
					{
						if (p is Triangle tri)
						{
							list.Add(new FlatTriangle
							{
								V0 = tri.Indexes[0],
								V1 = tri.Indexes[1],
								V2 = tri.Indexes[2]
							});
						}
					}
				}
				return list;
			}

			private static Dictionary<EdgeKey, List<int>> BuildAdjacency(List<FlatTriangle> tris)
			{
				var adj = new Dictionary<EdgeKey, List<int>>(tris.Count * 3);

				void Add(ushort a, ushort b, int t)
				{
					var key = new EdgeKey(a, b);
					if (!adj.TryGetValue(key, out var lst))
					{
						lst = new List<int>(2);
						adj[key] = lst;
					}
					lst.Add(t);
				}

				for (int i = 0; i < tris.Count; i++)
				{
					var t = tris[i];
					Add((ushort)t.V0, (ushort)t.V1, i);
					Add((ushort)t.V1, (ushort)t.V2, i);
					Add((ushort)t.V2, (ushort)t.V0, i);
				}

				return adj;
			}

			// ------------------------------------------------------------------------
			// strip builder (with A* / beam & legacy anchor packing)
			// ------------------------------------------------------------------------
			private StripBuildResult BuildStrips(
				List<FlatTriangle> tris,
				Dictionary<EdgeKey, List<int>> adj,
				int vertexCount,
				bool useAStar,
				bool useLegacyAnchors)
			{
				var stream = new List<StreamEntry>(tris.Count * 3);
				var triLookup = new Dictionary<int, (int, int)>(tris.Count);
				var usedGlobal = new bool[tris.Count];

				int realTriangleCount = 0;
				ushort maxFloatIndex = 0;

				int beamWidth = useAStar ? int.MaxValue : 8;

				for (int seed = 0; seed < tris.Count; seed++)
				{
					if (usedGlobal[seed])
						continue;

					var grown = GrowStripFromSeed(
						tris,
						adj,
						usedGlobal,
						seed,
						beamWidth,
						useLegacyAnchors);

					int baseIdx = stream.Count;
					stream.AddRange(grown.Stream);

					// record triangles
					for (int i = 0; i < grown.Triangles.Count; i++)
					{
						var tinfo = grown.Triangles[i];
						triLookup[tinfo.OriginalTriangle] = (1, baseIdx + tinfo.StreamIndex);
						realTriangleCount++;
					}

					// mark used
					foreach (int src in grown.SourceTriangles)
						usedGlobal[src] = true;

					// track max float
					for (int i = 0; i < grown.Stream.Count; i++)
					{
						ushort fi = grown.Stream[i].FloatIndex;
						if (fi > maxFloatIndex)
							maxFloatIndex = fi;
					}
				}

				// pack to bytes
				var streamBytes = new byte[stream.Count * 4];
				for (int i = 0; i < stream.Count; i++)
				{
					Array.Copy(BitConverter.GetBytes(stream[i].FloatIndex), 0, streamBytes, i * 4, 2);
					Array.Copy(BitConverter.GetBytes(stream[i].Flags), 0, streamBytes, i * 4 + 2, 2);
				}

				return new StripBuildResult
				{
					StreamBytes = streamBytes,
					TriangleCount = realTriangleCount,
					TriangleLookup = triLookup,
					MaxFloatIndex = maxFloatIndex
				};
			}

			private GrownStrip GrowStripFromSeed(
				List<FlatTriangle> tris,
				Dictionary<EdgeKey, List<int>> adj,
				bool[] usedGlobal,
				int seedIndex,
				int beamWidth,
				bool useLegacyAnchors)
			{
				var seed = tris[seedIndex];

				// initial candidate
				var init = new StripCandidate();
				init.Stream.Add(new StreamEntry { FloatIndex = (ushort)(seed.V0 * 6), Flags = 0 });
				init.Stream.Add(new StreamEntry { FloatIndex = (ushort)(seed.V1 * 6), Flags = 0 });
				init.Stream.Add(new StreamEntry { FloatIndex = (ushort)(seed.V2 * 6), Flags = 0 });
				init.Triangles.Add((seedIndex, 0));
				init.SourceTriangles.Add(seedIndex);
				init.Score = 1;

				var frontier = new List<StripCandidate> { init };
				var best = init;

				while (frontier.Count > 0)
				{
					// sort by score desc
					frontier.Sort((a, b) => b.Score.CompareTo(a.Score));
					if (frontier.Count > beamWidth)
						frontier.RemoveRange(beamWidth, frontier.Count - beamWidth);

					var cur = frontier[0];
					frontier.RemoveAt(0);

					if (cur.Score > best.Score)
						best = cur;

					if (cur.Stream.Count < 2)
						continue;

					ushort tailA = cur.Stream[cur.Stream.Count - 2].FloatIndex;
					ushort tailB = cur.Stream[cur.Stream.Count - 1].FloatIndex;

					// was the LAST entry already a legacy anchor?
					int streamCount = cur.Stream.Count;
					
						
					bool tailBIsLegacy = false;
					if (streamCount == 0)
					{ 
						tailBIsLegacy = false; 
					}
					else if (cur.Triangles.Count == 0 || (useLegacyAnchors && LegacyAnchors.Contains(tailB)))
					{
						tailBIsLegacy =  true; // we have stream entries but no triangles? treat as anchor tail
					}
					else
					{
						// last real triangle we added:
						var (lastTriIdx, lastTriStart) = cur.Triangles[cur.Triangles.Count - 1];
						int lastTriEnd = lastTriStart + 2; // triangles always use 3 consecutive entries

					// if the stream has grown past the last real triangle's end, the extra stuff is anchors
						 tailBIsLegacy = (streamCount - 1) > lastTriEnd;
					}

					// convert back to vertex ids (since adjacency is by vertex)
					int tailAV = tailA / 6;
					int tailBV = tailB / 6;
					var ek = new EdgeKey((ushort)tailAV, (ushort)tailBV);

					bool extended = false;

					if (adj.TryGetValue(ek, out var neigh))
					{
						for (int i = 0; i < neigh.Count; i++)
						{
							int triIdx = neigh[i];
							if (cur.SourceTriangles.Contains(triIdx)) continue;
							if (usedGlobal[triIdx]) continue;

							var nt = tris[triIdx];
							// find the third vertex (one that's not tailAV or tailBV)
							int thirdV;
							if (nt.V0 != tailAV && nt.V0 != tailBV) thirdV = nt.V0;
							else if (nt.V1 != tailAV && nt.V1 != tailBV) thirdV = nt.V1;
							else thirdV = nt.V2;

							var child = cur.Clone();

							// decide if we need to flip
							bool needsFlip = false;
							// simplest: if the natural order (tailA, tailB, third) is not found in nt, flip
							if (!((nt.V0 == tailAV && nt.V1 == tailBV && nt.V2 == thirdV) ||
								  (nt.V0 == tailBV && nt.V1 == thirdV && nt.V2 == tailAV)))
							{
								needsFlip = true;
							}

							short flags = needsFlip ? (short)(-1) : (short)0;
							int triStart = child.Stream.Count - 2;
							child.Stream.Add(new StreamEntry { FloatIndex = (ushort)(thirdV * 6), Flags = flags });
							child.Triangles.Add((triIdx, triStart));
							child.SourceTriangles.Add(triIdx);
							child.Score = child.Triangles.Count;

							frontier.Add(child);
							extended = true;
						}
					}

					if (!extended && useLegacyAnchors && !tailBIsLegacy)
					{
						var scored = new List<(ushort fi, int score)>();

						// 1) collect local neighbor vertices of tailBV
						var neighborVerts = new HashSet<ushort>();

						foreach (var kv in adj)
						{
							var e = kv.Key;
							
							if (e.A == tailBV) neighborVerts.Add(e.B);
							else if (e.B == tailBV) neighborVerts.Add(e.A);
						}

						// 2) score each neighbor as an anchor
						foreach (var neighV in neighborVerts)
						{
							// edge (tailBV, neighV)
							var ek2 = new EdgeKey((ushort)tailBV, neighV);

							int s = 0;
							if (adj.TryGetValue(ek2, out var trisOnEdge))
							{
								for (int i = 0; i < trisOnEdge.Count; i++)
								{
									int triIdx2 = trisOnEdge[i];
									if (!usedGlobal[triIdx2] && !cur.SourceTriangles.Contains(triIdx2))
										s++;
								}
							}

							// convert vertex -> float index (still unshifted here)
							ushort fi = (ushort)(neighV * 6);
							scored.Add((fi, s));
						}

						// 3) also mix in legacy anchors (they sometimes bridge tiny degenerates)
						foreach (var legacy in LegacyAnchors)
							scored.Add((legacy, 0));

						// 4) take best few
						const int K = 3;
						foreach (var (fi, s) in scored.OrderByDescending(x => x.score).Take(K))
						{
							var child = cur.Clone();
							child.Stream.Add(new StreamEntry { FloatIndex = fi, Flags = 0 });
							// keep same score, or slightly nudge
							child.Score = cur.Score;
							frontier.Add(child);
						}

						extended = true;
					}

					// if we still didn't extend, this candidate is dead
				}

				// convert best to grown
				var gs = new GrownStrip();
				gs.Stream.AddRange(best.Stream);
				gs.SourceTriangles.AddRange(best.SourceTriangles);
				gs.Triangles.AddRange(best.Triangles);
				return gs;
			}

			// ------------------------------------------------------------------------
			// internal data types
			// ------------------------------------------------------------------------
			private struct GrndVertex
			{
				public float X, Y, Z;
				public float NX, NY, NZ;
			}

			private sealed class TriangleSet
			{
				public int SetIndex;
				public int HeaderOffset;
				public int VertexBlockOffset;
				public int TriangleStreamOffset;
				public int TriangleCount;
				public List<StreamEntry> Stream;
			}

			private struct StreamEntry
			{
				public ushort FloatIndex;
				public short Flags;
			}

			private struct QuadRef
			{
				public ushort TriSet;
				public ushort TriIndex;
			}

			private sealed class QuadCell
			{
				public int Index;
				public List<QuadRef> Refs;
			}

			public sealed class DecodeResult
			{
				public GrndHeader Header;
				public Vertex[] Vertices;
				public Vertex[] Normals;
				public List<NJS_MESHSET> Meshes;
				public float BoundsXMin, BoundsXMax;
				public float BoundsZMin, BoundsZMax;
			}

			public struct GrndHeader
			{
				public float CenterX, CenterZ;
				public ushort GridX, GridZ;
				public ushort CellSizeX, CellSizeZ;
				public ushort TriangleSetCount;
				public ushort QuadCount;
			}

			private struct FlatTriangle
			{
				public int V0, V1, V2;
			}

			private readonly struct EdgeKey : IEquatable<EdgeKey>
			{
				public readonly ushort A;
				public readonly ushort B;

				public EdgeKey(ushort a, ushort b)
				{
					if (a < b) { A = a; B = b; }
					else { A = b; B = a; }
				}

				public bool Equals(EdgeKey other) => A == other.A && B == other.B;
				public override bool Equals(object obj) => obj is EdgeKey ek && Equals(ek);
				public override int GetHashCode() => (A << 16) ^ B;
			}

			private sealed class StripBuildResult
			{
				public byte[] StreamBytes;
				public int TriangleCount;
				public Dictionary<int, (int triSet, int triIndex)> TriangleLookup;
				public ushort MaxFloatIndex;
			}

			private sealed class GrownStrip
			{
				public List<StreamEntry> Stream = new List<StreamEntry>();
				public List<(int OriginalTriangle, int StreamIndex)> Triangles = new List<(int, int)>();
				public List<int> SourceTriangles = new List<int>();
			}

			private sealed class StripCandidate
			{
				public List<StreamEntry> Stream = new List<StreamEntry>();
				public List<(int OriginalTriangle, int StreamIndex)> Triangles = new List<(int, int)>();
				public HashSet<int> SourceTriangles = new HashSet<int>();
				public int Score;

				public StripCandidate Clone()
				{
					var c = new StripCandidate();
					c.Stream.AddRange(this.Stream);
					c.Triangles.AddRange(this.Triangles);
					c.SourceTriangles = new HashSet<int>(this.SourceTriangles);
					c.Score = this.Score;
					return c;
				}
			}
		}


		public class GRND
		{
			// For Reference, the setup for a GRND is as follows:
			// 0x00	- "GRND"
			// 0x04	- Chunk Size (Includes first 16 bytes).
			// 0x08	- Int; null[2]

			// GRND Header begins at 0x10 in a GRND Chunk. The GRND Chunk appears to be made up of a quad-tree to check for collision, followed by the actual
			// triangle/vertex data
			// 0x00	- Pointer to Triangles Chunk
			// 0x04	- Pointer to Quadtree Chunk
			// 0x08	- Float; X Pos 0,0
			// 0x0C	- Float; Z Pos 0,0
			// 0x10	- Short; X quad Number
			// 0x12	- Short; Z quad Number
			// 0x14	- Short; X quad Length
			// 0x16 - Short; Z quad Length
			// 0x18	- Short; Triangle Count
			// 0x1A	- Short; Poly Count

			/*
			 * GRND blocks contain a quad tree for quick lookup and collision detection
			 * It is made up of two chunks, a chunk for the quad tree, and a chunk for the polygons present in the GRND
			 * The each polygon in the polygon chunk is made up of a compressed list of triangle info, and a compressed list of vertices
			 * Since the polygon chunk uses compression to overlap triangle info and vertices, and the triangle indices which define all
			 * of the triangles are not listed, this algorithm uses the quad tree chunk to first identify all used triangle info (indices into the 
			 * triangle info block)
			*/

			public Vertex[] Vertices;
			public Vertex[] Normals;
			public List<NJS_MESHSET> Meshes;
			public Vertex Center;
			public short XCount;
			public short ZCount;
			public short XLen;
			public short ZLen;

			public short Trisets { get; private set; }
			public short QuadCount { get; private set; }

			public float XMin;
			public float XMax;
			public float ZMin;
			public float ZMax;

			public NJS_OBJECT ToObject()
			{
				NJS_OBJECT obj = new ();
					
				Vertex[] normals;
				if (Normals != null && Normals.Length == (Vertices?.Length ?? 0))
					normals = Normals;
				else
				{
					normals = new Vertex[Vertices?.Length ?? 0];
					for (int i = 0; i < normals.Length; i++)
						normals[i] = new Vertex(0, 1, 0);
				}

				BasicAttach attach = new(Vertices, normals, Meshes, Array.Empty<NJS_MATERIAL>());
				obj.Attach = attach;

				return obj;
			}

			public byte[] GetBytes(bool use_a_star, bool use_legacy_anchor_packing)
			{
				var codec = new GRNDCodec
				{
					// you can flip these from the caller if you want
					UseAStar = use_a_star,
					UseLegacyAnchorPacking = use_legacy_anchor_packing
				};
				return codec.Encode(this);
						}

			public GRND(ModelFile file, string name)
				{
				NJS_OBJECT obj = file.Model;

				BasicAttach attach = (BasicAttach)obj.Attach;
				Vertices = attach.Vertex;
				Meshes = attach.Mesh;
				Normals = attach.Normal;
					}
					
			public GRND(byte[] file, int address)
					{
				var codec = new GRNDCodec();
				var res = codec.Decode(file, address);

				// primary geometry
				this.Vertices = res.Vertices;
				this.Normals = res.Normals;
				this.Meshes = res.Meshes;

				// header-ish info (preserve what we can)
				this.Center = new Vertex(res.Header.CenterX, 0.0f, res.Header.CenterZ);
				this.XCount = (short)res.Header.GridX;
				this.ZCount = (short)res.Header.GridZ;
				this.XLen = (short)res.Header.CellSizeX;
				this.ZLen = (short)res.Header.CellSizeZ;
				this.Trisets = (short)res.Header.TriangleSetCount;
				this.QuadCount = (short)res.Header.QuadCount;

				// optional bounds — we can recompute if needed
				this.XMin = res.BoundsXMin;
				this.XMax = res.BoundsXMax;
				this.ZMin = res.BoundsZMin;
				this.ZMax = res.BoundsZMax;
			}
		}

		public class GOBJ
		{
			// For Reference, the setup for a GOBJ is as follows:
			// 0x00	- "GOBJ"
			// 0x04	- Chunk Size (Includes first 16 bytes),
			// 0x08	- Int; null[2]

			// GOBJ "Header" begins at 0x10 in a GOBJ Chunk.
			// 0x00	- NJS_OBJECT
			// NJS_OBJECT should have a child.
			// Said child node will have a ChunkAttach/NJS_MODEL_CNK, the child pointer is set but it also seems to always follow the first NJS_OBJECT.
			// As stated above, all pointers are relative to the location of the pointer EXCEPT for the ChunkAttach Pointer for the child.
			// It has a 1 which does not correspond to the ChunkAttach/NJS_MODEL_CNK's location.
			// Its location will be immediately after the child NJS_OBJECT.
			// It's also in a flipped order. The Center/Radius comes first, then the VertexChunk pointer, and the PolyChunk pointer at the end.

			public NJS_OBJECT Object;
			public BoundingSphere Bounds;
			public NJS_OBJECT GroundObject;

			public GOBJ(byte[] file, int address)
			{                   
				int addr = 16;
				GroundObject = get_GOBJ_node(file, addr);
			}

			private NJS_OBJECT get_GOBJ_node(byte[] file, int address)
			{
				NJS_OBJECT obj = new NJS_OBJECT();
				int data_ptr = ByteConverter.ToInt32(file, address);

				obj.Position = new Vertex(file, address + 0x8);
				obj.Rotation = new Rotation(file, address + 0x14);
				obj.Scale = new Vertex(file, address + 0x20);

				int leftptr = ByteConverter.ToInt32(file, address + 0x2c);
				if (leftptr > 0)
				{
					leftptr += 0x2c + address;
					obj.AddChild(get_GOBJ_node(file, leftptr));
				}

				int rightptr = ByteConverter.ToInt32(file, address + 0x30);
				if (rightptr > 0)
				{
					rightptr += 0x2c + address;
					obj.AddChild(get_GOBJ_node(file, rightptr));
				}

				if (data_ptr != 0)
				{
					data_ptr += address;
					ChunkAttach attach = new ChunkAttach(true, true);
					attach.Bounds = new BoundingSphere(file, data_ptr);
					data_ptr += 0x10;

					int vertptr = ByteConverter.ToInt32(file, data_ptr) + data_ptr;
					int polyptr = data_ptr + 76;

					//The geometry structure may not be in the correct format, but leaving this here for now
					VertexChunk vertexchunk = new VertexChunk(file, vertptr);
					PolyChunk polychunk = PolyChunk.Load(file, polyptr);

					attach.Vertex.Add(vertexchunk);
					attach.Poly.Add(polychunk);

					obj.Attach = attach;
				}
				return obj;
			}
		}

		public string Name;
		public GroundType Type;
		public byte[] File;
		public NJS_OBJECT ConvertedObject;

		private GRND GRNDObj;
		//private GOBJ GOBJChunk; // TODO: Implement GOBJChunk reading proper.

		public nmldGround()
		{

		}

		public nmldGround(byte[] file, int address, string name)
		{
			// These chunks are actually condensed chunk models.
			// GOBJ has actual NJS_OBJECTs and a "flipped" ChunkAttach/NJS_MODEL_CNK.
			// GRND does not, but does seem to have possible grid set bounds in the custom header.
			// Both use pointers that are relative to the position of the pointer in the file. 
			// Switch Case includes comments on the structures.

			string magic = Encoding.ASCII.GetString(file, address, 4);

			int filesize = ByteConverter.ToInt32(file, address + 4);

			File = new byte[filesize];
			Array.Copy(file, address, File, 0, filesize);

			Name = name + "_" + magic;

			switch (magic)
			{
				case "GRND":
					Type = GroundType.Ground;
					GRNDObj = new GRND(File, 0);
					break;
				case "GOBJ":

					Type = GroundType.GroundObject;
					//GOBJChunk = new GOBJ(File, 0);
					break;
				default:
					Console.WriteLine("Unknown Ground Format Found: %s", magic);
					Type = GroundType.Unknown;
					break;
			}

			// Currently non-function due to weird poly format.
			// Can uncomment once conversion is fixed.
			if (Type == GroundType.Ground)
			{
				ConvertedObject = GRNDObj.ToObject();
			}
			//if (Type == GroundType.GroundObject)
			//{
			//	ConvertedObject = GOBJChunk.;
			//}
		}

		static public nmldGround FromGrndFile(byte[] file, string name, bool use_a_star, bool use_legacy_anchor_packing)
			{
			nmldGround grnd = new nmldGround();

			grnd.Name = name;
			if (name.Contains("GOBJ"))
			{ 
				grnd.File = file;
				grnd.Type = GroundType.GroundObject;
				return grnd;
			} else if (name.Contains("GUNK"))
			{
				grnd.File = file;
				grnd.Type = GroundType.Unknown;
				return grnd;
			}

			grnd.Type = GroundType.Ground;
			ModelFile obj = new ModelFile(file, name);
			grnd.GRNDObj = new GRND(obj, name);
			grnd.File = grnd.GRNDObj.GetBytes(use_a_star, use_legacy_anchor_packing);

			return grnd;
		}
	}

	public class nmldMotion
	{
		public enum MotionType
		{
			Node = 0,
			Shape = 1,
			Camera = 2,
			Unknown
		}

		public string Name;
		public MotionType Type;
		public byte[] File;

		public string GetTypeString()
		{
			switch (Type)
			{
				case MotionType.Node:
					return "_motion";
				case MotionType.Shape:
					return "_shape";
				case MotionType.Camera:
					return "_camera";
				default:
					return "_unknown";
			}
		}

		public nmldMotion(byte[] file, int address, string name, string idx)
		{
			string magic = Encoding.ASCII.GetString(file, address, 4);

			switch (magic)
			{
				case "NMDM":
					Type = MotionType.Node;
					break;
				case "NSSM":
					Type = MotionType.Shape;
					break;
				case "NCAM":
					Type = MotionType.Camera;
					break;
				default:
					Console.WriteLine("Unidentified Motion Type: %s", magic);
					Type = MotionType.Unknown;
					break;
			}

			Name = name + GetTypeString() + "_" + idx;

			int njmsize = ByteConverter.ToInt32(file, address + 4) + 8;
			int pofsize = ByteConverter.ToInt32(file, address + njmsize + 4) + 8;

			File = new byte[njmsize + pofsize];
			Array.Copy(file, address, File, 0, njmsize + pofsize);
		}
	}

	public class nmldTextureList
	{
		public string Name;
		public NJS_TEXLIST TexList;

		public nmldTextureList()
		{
			Name = string.Empty;
			TexList = new NJS_TEXLIST();
		}

		public nmldTextureList(byte[] file, int address, string name)
		{
			TexList = NJS_TEXLIST.Load(file, address, 0);

			Name = name + ".tls";
		}
	}

	public class nmldEntry
	{
		public int Index { get; set; } = 0;
		public int TblID { get; set; } = 0;
		public List<int> GroundLinks { get; set; } = new();
		public List<int> ParamList2 { get; set; } = new();
		public List<int> FunctionParameters { get; set; } = new();

		public List<int> ObjectAddresses { get; set; } = new();
		public List<int> MotionAddresses { get; set; } = new();
		public List<int> GroundAddresses { get; set; } = new();
		public nmldTextureList Texlist { get; set; } = new();

		public List<string> ObjectFilenames { get; set; } = new();
		public List<string> MotionFilenames { get; set; } = new();
		public List<string> GroundFilenames { get; set; } = new();
		public List<string> TexFilenames { get; set; } = new();

		public string Fxn { get; set; } = string.Empty;
		public Vertex Position { get; set; } = new();
		public Vertex Rotation { get; set; } = new();
		public Vertex Scale { get; set; } = new();

		public string GetNameWithoutIndex()
		{
			string bitID = "";
			if (Fxn == "eventhook")
			{
				bitID = FunctionParameters[FunctionParameters.Count - 1].ToString();
			}
			return Index.ToString("D3") + "_" + Fxn + bitID;
		}

		public string GetNameAndIndex(int index)
		{
			string bitID = "";
			if (Fxn == "eventhook")
			{
				bitID = FunctionParameters[FunctionParameters.Count - 1].ToString();
			}
			return Index.ToString("D3") + "_" + Fxn + bitID + "_" + index.ToString("D2");
		}

		private void GetParamList(byte[] file, int offset, List<int> target_var)
		{
			int count = ByteConverter.ToInt32(file, offset);

			for (int i = 0; i < count; i ++)
			{
				target_var.Add(ByteConverter.ToInt32(file, offset + i * 4 + 4));
			}
		}

		private void GetObjects(byte[] file, int offset)
		{
			int count = ByteConverter.ToInt32(file, offset);

			for (int i = 0; i < count; i++)
			{
				int address = ByteConverter.ToInt32(file, offset + (4 * (i + 1)));
				
				if (address != 0)
				{
					ObjectAddresses.Add(address);
				}
			}
		}

		private void GetMotions(byte[] file, int offset)
		{
			int count = ByteConverter.ToInt32(file, offset);

			for (int i = 0; i < count; i++)
			{
				int address = ByteConverter.ToInt32(file, offset + (4 * (i + 1)));

				if (address != 0)
				{
					MotionAddresses.Add(address);
			}
			}
		}

		private void GetGrounds(byte[] file, int offset)
		{
			int count = ByteConverter.ToInt32(file, offset);

			for (int i = 0; i < count; i++)
			{
				int address = ByteConverter.ToInt32(file, offset + (4 * (i + 1)));

				if (address != 0)
				{
					GroundAddresses.Add(address);
				}
			}
		}

		private void GetTextures(byte[] file, int offset)
		{
			Texlist = new nmldTextureList(file, offset, GetNameWithoutIndex());
			TexFilenames = Texlist.TexList.TextureNames.ToList();
		}

		public string WriteEntryInfo()
		{
			StringBuilder sb = new StringBuilder();

			for (int i = 0; i < ObjectAddresses.Count; i++)
			{
				sb.AppendLine(
					GetNameAndIndex(i) +
					", " + Position.ToString() +
					", " + Rotation.ToString() +
					", " + Scale.ToString());
			}

			for (int i = 0;i < GroundAddresses.Count; i++){
				sb.AppendLine(
					GetNameAndIndex(i) +
					", " + Position.ToString() + 
					", " + Rotation.ToString() + 
					", " + Scale.ToString());
			}

			return sb.ToString();
		}

		public IniGroup GetManifestInfo()
		{
			IniGroup manifest_entry = new IniGroup();

			manifest_entry.Add("EntryID", Index.ToString("D3"));
			manifest_entry.Add("TblID", TblID.ToString("X4"));
			manifest_entry.Add("Fxn", Fxn);

			if (GroundLinks.Count > 0) {
				manifest_entry.Add("GroundLinks", IntListToManifestValue(GroundLinks));
			}
			
			if (ParamList2.Count > 0)
			{
				manifest_entry.Add("ParamList2", IntListToManifestValue(ParamList2));
			}
			
			if (FunctionParameters.Count > 0)
			{
				manifest_entry.Add("FunctionParameters", IntListToManifestValue(FunctionParameters));
			}

			if (ObjectFilenames.Count > 0)
			{
				manifest_entry.Add("NJs", StringListToManifestValue(ObjectFilenames));
			}

			if (MotionFilenames.Count > 0)
			{
				manifest_entry.Add("Motions", StringListToManifestValue(MotionFilenames));
			}

			if (GroundFilenames.Count > 0)
			{
				manifest_entry.Add("Grnds", StringListToManifestValue(GroundFilenames));
			}

			if (TexFilenames.Count > 0)
			{
				manifest_entry.Add("Textures", StringListToManifestValue(TexFilenames));
			}

			manifest_entry.Add("Position", Position.ToString());
			manifest_entry.Add("Rotation", Rotation.ToString());
			manifest_entry.Add("Scale", Scale.ToString());

			return manifest_entry;
		}

		public nmldEntry()
		{
			GroundLinks = new();
			ParamList2 = new();
			FunctionParameters = new();
			ObjectAddresses = new();
			GroundAddresses = new();
			MotionAddresses = new();
			ObjectFilenames = new();
			GroundFilenames = new();
			MotionFilenames = new();
			Texlist = new();
			Fxn = "";
			Position = new();
			Rotation = new();
			Scale = new();
			Index = 0xFFFF;
			TblID = 0xFFFF;
		}

		public nmldEntry(int offset, byte[] file)
		{
			Index = ByteConverter.ToInt32(file, offset);
			TblID = ByteConverter.ToInt32(file, offset + 4);	

			int ptrGroundLinks = ByteConverter.ToInt32(file, offset + 0x8);
			GetParamList(file, ptrGroundLinks, GroundLinks);
			int ptrParamList2 = ByteConverter.ToInt32(file, offset + 0xc);
			GetParamList(file, ptrParamList2, ParamList2);
			int ptrFunctionParameters = ByteConverter.ToInt32(file, offset + 0x10);
			GetParamList(file, ptrFunctionParameters, FunctionParameters);

			// Get Entry Objects
			int ptrObjects = ByteConverter.ToInt32(file, offset + 0x14);
			if (ByteConverter.ToInt32(file, ptrObjects + 4) != 0)
				GetObjects(file, ptrObjects);

			// Get Entry Grounds
			int ptrGrounds = ByteConverter.ToInt32(file, offset + 0x18);
			if (ByteConverter.ToInt32(file, ptrGrounds + 4) != 0)
				GetGrounds(file, ptrGrounds);

			// Get Entry Motions
			int ptrMotions = ByteConverter.ToInt32(file, offset + 0x1C);
			if (ByteConverter.ToInt32(file, ptrMotions) != 0)
				GetMotions(file, ptrMotions);

			// Get Entry Textures
			int ptrTextures = ByteConverter.ToInt32(file, offset + 0x20);
			if (ByteConverter.ToInt32(file, ptrTextures + 4) != 0)
				GetTextures(file, ptrTextures);

			// Get Entry Name
			int namesize = 0;
			for (int s = 0; s < 0x14; s++)
			{
				if (file[offset + 0x24 + s] != 0)
					namesize++;
				else
					break;
			}
			byte[] namechunk = new byte[namesize];
			Array.Copy(file, offset + 0x24, namechunk, 0, namesize);
			Fxn = Encoding.ASCII.GetString(namechunk);

			// 0x38 - 0x43 is reserved for use by the game. A pointer to the data 

			Position	= new Vertex(ByteConverter.ToSingle(file, offset + 0x44), ByteConverter.ToSingle(file, offset + 0x48), ByteConverter.ToSingle(file, offset + 0x4C));
			Rotation	= new Vertex(ByteConverter.ToSingle(file, offset + 0x50), ByteConverter.ToSingle(file, offset + 0x54), ByteConverter.ToSingle(file, offset + 0x58));
			Scale		= new Vertex(ByteConverter.ToSingle(file, offset + 0x5C), ByteConverter.ToSingle(file, offset + 0x60), ByteConverter.ToSingle(file, offset + 0x64));

		}

		private static string IntListToManifestValue(List<int> list)
		{
			StringBuilder gl = new StringBuilder();
			for (int i = 0; i < list.Count; i++)
			{
				if (i > 0) gl.Append(',');
				gl.Append(list[i].ToString("X8"));
			}
			return gl.ToString();
		}

		private static List<int> IntListFromManifestValue(string value)
		{
			if (value.Length == 0) return [];
			List<int> list = [];
			string[] strs = value.Split(',');
			foreach (string str in strs)
			{
				list.Add(int.Parse(str, System.Globalization.NumberStyles.HexNumber));
			}
			return list;
		}

		private static string StringListToManifestValue(List<string> list)
		{
			return String.Join(',', list);
		}

		private static List<string> StringListFromManifestValue(string value)
		{
			if (value.Length == 0) return [];
			return value.Split(',').ToList();
		}

		internal static nmldEntry FromManifest(string key, IniGroup entry_ini)
		{
			nmldEntry entry = new();
			entry.Index = int.Parse(key);
			entry.TblID = int.Parse(entry_ini["TblID"], System.Globalization.NumberStyles.HexNumber);
			if (entry_ini.ContainsKey("GroundLinks")) entry.GroundLinks = IntListFromManifestValue(entry_ini["GroundLinks"]);
			if (entry_ini.ContainsKey("ParamList2")) entry.ParamList2 = IntListFromManifestValue(entry_ini["ParamList2"]);
			if (entry_ini.ContainsKey("FunctionParameters")) entry.FunctionParameters = IntListFromManifestValue(entry_ini["FunctionParameters"]);
			if (entry_ini.ContainsKey("NJs")) entry.ObjectFilenames = StringListFromManifestValue(entry_ini["NJs"]);
			if (entry_ini.ContainsKey("Motions")) entry.MotionFilenames = StringListFromManifestValue(entry_ini["Motions"]);
			if (entry_ini.ContainsKey("Grnds")) entry.GroundFilenames = StringListFromManifestValue(entry_ini["Grnds"]);
			if (entry_ini.ContainsKey("Textures")) entry.TexFilenames = StringListFromManifestValue(entry_ini["Textures"]);
			entry.Fxn = entry_ini["Fxn"];
			entry.Position = new Vertex(entry_ini["Position"]);
			entry.Rotation = new Vertex(entry_ini["Rotation"]);
			entry.Scale = new Vertex(entry_ini["Scale"]);

			return entry;
	}

	public class nmldArchiveFile
	{
		public string Name { get; set; } = string.Empty;
		public List<nmldEntry> Entries { get; set; } = new();
		public PuyoFile TextureFile { get; set; }

		private void GetTextureArchive(byte[] file, int offset)
		{
			Console.WriteLine("Getting Textures...");
			if (ByteConverter.BigEndian == true)
				TextureFile = new PuyoFile(PuyoArchiveType.GVMFile);
			else
				TextureFile = new PuyoFile();

			int numtex = ByteConverter.ToInt32(file, offset);
			int texnamearray = offset + 4;
			Dictionary<string, int> texnames = new();

			if (numtex > 0)
			{
				Console.WriteLine("Textures Found! Creating Archive.");
				for (int i = 0; i < numtex; i++)
				{
					int element = texnamearray + (i * 44);
					texnames.Add(file.GetCString(element, Encoding.UTF8), ByteConverter.ToInt32(file, element + 40));
				}

				// Texture Embeds have an unspecified spacing between the end of the names and the start of the texture data.
				// So we do this to get through the padding
				int texdataoffset = offset + 4 + numtex * 44;
				if (file[texdataoffset] == 0)
				{
					do
					{
						texdataoffset += 1;
					}
					while (file[texdataoffset] == 0);
				}
				int texdataptr = texdataoffset;

				bool isBig = ByteConverter.BigEndian;

				foreach (KeyValuePair<string, int> tex in texnames)
				{
					ByteConverter.BigEndian = false;
					int texdataptr2 = texdataptr;
					string magic = Encoding.ASCII.GetString(file, texdataptr2, 4);
					int size = 0;

					switch (magic)
					{
						case "GBIX":
						case "GCIX":
							size += ByteConverter.ToInt32(file, texdataptr2 + 4) + 8;
							texdataptr2 += 16;
							break;
					}

					size += ByteConverter.ToInt32(file, texdataptr2 + 4) + 8;
					byte[] texture = new byte[size];
					Array.Copy(file, texdataptr, texture, 0, size);

					switch (TextureFile.Type)
					{
						case PuyoArchiveType.PVMFile:
							TextureFile.Entries.Add(new PVMEntry(texture, tex.Key));
							break;
						case PuyoArchiveType.GVMFile:
							TextureFile.Entries.Add(new GVMEntry(texture, tex.Key));
							break;
					}

					texdataptr += tex.Value;
				}

				ByteConverter.BigEndian = isBig;
			}
		}

		private void GetEntries(byte[] file, int offset, int count)
		{
			for (int i = 0; i < count; i++)
			{
				Entries.Add(new nmldEntry(offset + (i * 104), file));
			}
		}

		public nmldArchiveFile()
		{
			Name = string.Empty;
			Entries = new List<nmldEntry>();
			TextureFile = new();
		}

		public nmldArchiveFile(byte[] file, string name)
		{
			Name = name;

			int nmldCount		= ByteConverter.ToInt32(file, 0);
			int ptr_nmldTable	= ByteConverter.ToInt32(file, 0x04);
			int ptr_fxnparams	= ByteConverter.ToInt32(file, 0x08);
			int realdatapointer = ByteConverter.ToInt32(file, 0x0C);
			int textablepointer = ByteConverter.ToInt32(file, 0x10);
			Console.WriteLine("Number of NMLD entries: {0}, NMLD data starts at {1}, real data starts at {2}", nmldCount, ptr_nmldTable.ToString("X"), realdatapointer.ToString("X"));

			// Go ahead and extract the texture archive.
			GetTextureArchive(file, textablepointer);

			// Collect Entries and their contents
			GetEntries(file, ptr_nmldTable, nmldCount);
		}
	}

	public class MLDArchive : GenericArchive
	{
		public override void CreateIndexFile(string path)
		{
			return;
		}

		public class MLDArchiveEntry : GenericArchiveEntry
		{

			public override Bitmap GetBitmap()
			{
				throw new NotImplementedException();
			}

			public MLDArchiveEntry(byte[] data, string name)
			{
				Name = name;
				Data = data;
			}
		}

		private void ExtractEntries(nmldArchiveFile archive, string directory)
		{
			StringBuilder sb = new StringBuilder();

			// Add Entries
			foreach (nmldEntry entry in archive.Entries)
			{
				// Add Objects
				foreach (nmldObject model in entry.Objects)
				{
					Entries.Add(new MLDArchiveEntry(model.File, model.Name + ".nj"));
				}

				// Add Ground/Ground Object Files
				foreach (nmldGround ground in entry.Grounds)
				{
					ModelFile mfile = new ModelFile(ModelFormat.Basic, ground.ConvertedObject, null, null);
					switch (ground.Type)
					{
						case nmldGround.GroundType.Ground:
							Entries.Add(new MLDArchiveEntry(mfile.GetBytes(Path.Combine(directory, ground.Name + ".grnd.sa2mdl")), ground.Name + ".grnd.sa2mdl"));
							// mfile.SaveToFile(Path.Combine(directory, ground.Name + ".grnd.sa2mdl"));
							break;
						case nmldGround.GroundType.GroundObject:
							//Entries.Add(new MLDArchiveEntry(ground.File, ground.Name + ".gobj"));
							//mfile.SaveToFile(Path.Combine(directory, ground.Name + ".gobj.sa2mdl"));
							break;
						case nmldGround.GroundType.Unknown:
							Entries.Add(new MLDArchiveEntry(ground.File, ground.Name + ".gunk"));
							break;
					}
				}

				// Add Motions
				foreach (nmldMotion motion in entry.Motions)
				{
					switch (motion.Type)
					{
						case nmldMotion.MotionType.Node:
							Entries.Add(new MLDArchiveEntry(motion.File, motion.Name + ".njm"));
							break;
						case nmldMotion.MotionType.Shape:
							Entries.Add(new MLDArchiveEntry(motion.File, motion.Name + ".njs"));
							break;
						case nmldMotion.MotionType.Camera:
							Entries.Add(new MLDArchiveEntry(motion.File, motion.Name + ".njc"));
							break;
						case nmldMotion.MotionType.Unknown:
							Entries.Add(new MLDArchiveEntry(motion.File, motion.Name + ".num"));
							break;
					}
				}

				// Save Texlist
				if (entry.Texlist.TexList.NumTextures > 0)
				{
					if (!Directory.Exists(directory))
						Directory.CreateDirectory(directory);

					entry.Texlist.TexList.Save(Path.Combine(directory, entry.Texlist.Name));
				}

				sb.Append(entry.WriteEntryInfo());
			}

			// Add Info File
			Entries.Add(new MLDArchiveEntry(Encoding.ASCII.GetBytes(sb.ToString()), "FileInfo.amld"));

			// Add Texture Archive
			if (archive.TextureFile != new PuyoFile())
			{
				string ext = "";
				switch (archive.TextureFile.Type)
				{
					case PuyoArchiveType.PVMFile:
						ext = ".pvm";
						break;
					case PuyoArchiveType.GVMFile:
						ext = ".gvm";
						break;
				}
				Entries.Add(new MLDArchiveEntry(archive.TextureFile.GetBytes(), archive.Name + ext));
			}
		}

		public MLDArchive(string filepath, byte[] file)
		{
			string directory = Path.Combine(Path.GetDirectoryName(filepath), Path.GetFileNameWithoutExtension(filepath));
			string filename = Path.GetFileNameWithoutExtension(filepath);
			string aklzcheck = Encoding.ASCII.GetString(file, 0, 4);
			if (aklzcheck == "AKLZ")
				ByteConverter.BigEndian = true;
			else
				ByteConverter.BigEndian = SplitTools.HelperFunctions.CheckBigEndianInt32(file, 0xC);

			nmldArchiveFile archive;

			if (ByteConverter.BigEndian)
			{
				Console.WriteLine("Skies of Arcadia: Legends MLD File");

				if (aklzcheck == "AKLZ")
				{
					Console.WriteLine("MLD Archive is Compressed. Decompressing...");
					byte[] dfile = new byte[0];

					// Decompress File Here
					using (Stream stream = new MemoryStream(file))
					{
						using (MemoryPoolStream pool = new AKLZ().Decompress(stream))
						{
							dfile = new byte[pool.ToArray().Length];
							Array.Copy(pool.ToArray(), dfile, pool.ToArray().Length);
						}
					}

					if (dfile.Length > 0)
					{
						Console.WriteLine("File Decompressed, saving and reading decompressed archive.");
						Entries.Add(new MLDArchiveEntry(dfile, ("..\\" + filename + "_dec.mld")));
						archive = new nmldArchiveFile(dfile, filename);
					}
					else
					{
						Console.WriteLine("Decompression Failed.");
						archive = new();
					}
				}
				else
					archive = new nmldArchiveFile(file, filename);
			}
			else
			{
				Console.WriteLine("Skies of Arcadia MLD File");
				archive = new nmldArchiveFile(file, filename);
			}

			if (archive != new nmldArchiveFile())
			{
				ExtractEntries(archive, directory);
			}
			else
				Console.WriteLine("Unable to read archive.");
		}

		public override byte[] GetBytes()
		{
			throw new NotImplementedException();
		}
	}
}
