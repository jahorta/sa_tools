﻿using System;
using System.Collections.Generic;
using System.Drawing;

using Microsoft.DirectX;
using Microsoft.DirectX.Direct3D;

using SonicRetro.SAModel.Direct3D;

namespace SonicRetro.SAModel.SAEditorCommon.UI
{
	/// <summary>
	/// Point Helpers are useful for displaying and manipulating verts in 3d space.
	/// </summary>
	public class PointHelper
	{
		#region Local Vars
		bool enabled;
		bool drawCube = false;
		bool scaleHandlesToCam = false;
		float handleSize = 20f;
		Vertex affectedPoint;
		GizmoSelectedAxes selectedAxes;
		#endregion

		#region Public Accessors
		public bool Enabled { get { return enabled; } set { enabled = value; } }
		public GizmoSelectedAxes SelectedAxes { get { return selectedAxes; } set { selectedAxes = value; } }
		/// <summary>If TRUE, the point Helper will render a small, solid cube for positional/depth reference.</summary>
		public bool DrawCube { get { return drawCube; } set { drawCube = value; } }
		/// <summary>Texture to use if DrawCube is TRUE.</summary>
		public Texture BoxTexture { get; set; }
		#endregion

		/// <summary>
		/// Create a new point helper.
		/// </summary>
		public PointHelper()
		{
			enabled = false;
			selectedAxes = GizmoSelectedAxes.NONE;
		}

		public void SetPoint(Vertex point)
		{
			affectedPoint = point;
			enabled = true;
			selectedAxes = GizmoSelectedAxes.NONE;
		}

		/// <summary>
		/// Determines which axes have been selected by a hovering mouse.
		/// </summary>
		/// <param name="Near"></param>
		/// <param name="Far"></param>
		/// <param name="Viewport"></param>
		/// <param name="Projection"></param>
		/// <param name="View"></param>
		/// <param name="cam">viewport camera</param>
		/// <returns></returns>
		public GizmoSelectedAxes CheckHit(Vector3 Near, Vector3 Far, Viewport Viewport, Matrix Projection, Matrix View, EditorCamera cam)
		{
			if (!enabled) return GizmoSelectedAxes.NONE;

			MatrixStack transform = new MatrixStack();
			transform.Push();

			float dist = cam.Position.Distance(affectedPoint.ToVector3()) * 0.0825f;

			transform.TranslateLocal(affectedPoint.X, affectedPoint.Y, affectedPoint.Z);
			if (scaleHandlesToCam)
				transform.ScaleLocal(Math.Abs(dist), Math.Abs(dist), Math.Abs(dist));
			else
				transform.ScaleLocal(handleSize, handleSize, handleSize);

			Vector3 pos = Vector3.Unproject(Near, Viewport, Projection, View, transform.Top);
			Vector3 dir = Vector3.Subtract(pos, Vector3.Unproject(Far, Viewport, Projection, View, transform.Top));
			IntersectInformation info;

			if (Gizmo.XMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.X_AXIS;
			if (Gizmo.YMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.Y_AXIS;
			if (Gizmo.ZMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.Z_AXIS;
			if (Gizmo.XYMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.XY_AXIS;
			if (Gizmo.ZXMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.XZ_AXIS;
			if (Gizmo.ZYMoveMesh.Intersect(pos, dir, out info)) return GizmoSelectedAxes.ZY_AXIS;

			return GizmoSelectedAxes.NONE;
		}

		/// <summary>
		/// Draws the gizmo onscreen.
		/// </summary>
		/// <param name="d3ddevice"></param>
		/// <param name="cam"></param>
		public void Draw(Device d3ddevice, EditorCamera cam)
		{
			if ((affectedPoint == null) || (!enabled))
				return;

			d3ddevice.RenderState.ZBufferEnable = true;
			d3ddevice.BeginScene();

			RenderInfo.Draw(Render(d3ddevice, new MatrixStack(), cam), d3ddevice, cam);

			d3ddevice.EndScene(); //all drawings before this line
			//d3ddevice.Present();
		}

		public void DrawBox(Device d3ddevice, EditorCamera cam)
		{
			if (!enabled || !drawCube)
				return;

			BoundingSphere gizmoSphere = new BoundingSphere() { Center = new Vertex(affectedPoint.X, affectedPoint.Y, affectedPoint.Z), Radius = handleSize };

			MatrixStack transform = new MatrixStack();

			transform.Push();
			transform.TranslateLocal(affectedPoint.X, affectedPoint.Y, affectedPoint.Z);
			transform.ScaleLocal(handleSize, handleSize, handleSize);
			RenderInfo boxRenderInfo = new RenderInfo(Gizmo.BoxMesh, 0, transform.Top, Gizmo.StandardMaterial, BoxTexture, FillMode.Solid, gizmoSphere);

			RenderInfo.Draw(new List<RenderInfo>() { boxRenderInfo }, d3ddevice, cam);
			transform.Pop();
		}

		// TODO: Consider returning IEnumerable<RenderInfo>
		private RenderInfo[] Render(Device dev, MatrixStack transform, EditorCamera cam)
		{
			List<RenderInfo> result = new List<RenderInfo>();

			if (!enabled)
				return result.ToArray();

			float dist = cam.Position.Distance(affectedPoint.ToVector3()) * 0.0825f;
			BoundingSphere gizmoSphere = new BoundingSphere() { Center = new Vertex(affectedPoint.X, affectedPoint.Y, affectedPoint.Z), Radius = (1.0f * Math.Abs(dist)) };

			#region Setting Render States
			dev.SetSamplerState(0, SamplerStageStates.MinFilter, (int)TextureFilter.Point); // no fancy filtering is required because no textures are even being used
			dev.SetSamplerState(0, SamplerStageStates.MagFilter, (int)TextureFilter.Point);
			dev.SetSamplerState(0, SamplerStageStates.MipFilter, (int)TextureFilter.Point);
			dev.SetRenderState(RenderStates.Lighting, true);
			dev.SetRenderState(RenderStates.SpecularEnable, false);
			dev.SetRenderState(RenderStates.Ambient, Color.White.ToArgb());
			dev.SetRenderState(RenderStates.AlphaBlendEnable, false);
			dev.SetRenderState(RenderStates.ColorVertex, false);
			dev.Clear(ClearFlags.ZBuffer, 0, 1, 0);
			#endregion

			transform.Push();
			transform.TranslateLocal(affectedPoint.X, affectedPoint.Y, affectedPoint.Z);
			if (scaleHandlesToCam) transform.ScaleLocal(Math.Abs(dist), Math.Abs(dist), Math.Abs(dist));
			else transform.ScaleLocal(handleSize, handleSize, handleSize);

			#region Creating Render Info
			RenderInfo xRenderInfo = new RenderInfo(Gizmo.XMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.X_AXIS) ? Gizmo.HighlightMaterial : Gizmo.XMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(xRenderInfo);
			RenderInfo yRenderInfo = new RenderInfo(Gizmo.YMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.Y_AXIS) ? Gizmo.HighlightMaterial : Gizmo.YMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(yRenderInfo);
			RenderInfo zRenderInfo = new RenderInfo(Gizmo.ZMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.Z_AXIS) ? Gizmo.HighlightMaterial : Gizmo.ZMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(zRenderInfo);
			RenderInfo xyRenderInfo = new RenderInfo(Gizmo.XYMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.XY_AXIS) ? Gizmo.HighlightMaterial : Gizmo.DoubleAxisMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(xyRenderInfo);
			RenderInfo zxRenderInfo = new RenderInfo(Gizmo.ZXMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.XZ_AXIS) ? Gizmo.HighlightMaterial : Gizmo.DoubleAxisMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(zxRenderInfo);
			RenderInfo zyRenderInfo = new RenderInfo(Gizmo.ZYMoveMesh, 0, transform.Top, (selectedAxes == GizmoSelectedAxes.ZY_AXIS) ? Gizmo.HighlightMaterial : Gizmo.DoubleAxisMaterial, null, FillMode.Solid, gizmoSphere);
			result.Add(zyRenderInfo);
			#endregion

			transform.Pop();
			return result.ToArray();
		}

		/// <summary>
		/// Transforms the Items that belong to this Gizmo.
		/// </summary>
		/// <param name="xChange">Input for x axis.</param>
		/// <param name="yChange">Input for y axis.</param>
		/// <returns>TRUE if an operation was performed, FALSE if nothing was done.</returns>
		public bool TransformAffected(float xChange, float yChange, EditorCamera cam)
		{
			// don't operate with an invalid axis seleciton, or invalid mode
			if ((selectedAxes == GizmoSelectedAxes.NONE) || (!enabled))
				return false;

			float yFlip = -1; // I don't think we'll ever need to mess with this
			float xFlip = 1; // TODO: Depending on the orientation of the camera, this will need to be flipped.
							// consider using the cross product of the camera's look vector and the handle's position to determine
							// if the flip is needed.

			float xOff = 0.0f, yOff = 0.0f, zOff = 0.0f, axisDot = 0.0f;

			Vector3 axisDirection = new Vector3();

			switch (selectedAxes)
			{
				case GizmoSelectedAxes.X_AXIS:
					axisDirection = new Vector3(1, 0, 0);
					axisDot = Vector3.Dot(cam.Look, axisDirection);
					xFlip = (axisDot > 0) ? 1 : -1;
					xOff = xChange * xFlip;
					break;
				case GizmoSelectedAxes.Y_AXIS:
					axisDirection = new Vector3(0, 1, 0);
					axisDot = Vector3.Dot(cam.Look, axisDirection);
					yOff = yChange * yFlip;
					break;
				case GizmoSelectedAxes.Z_AXIS:
					axisDirection = new Vector3(0, 0, 1);
					axisDot = Vector3.Dot(cam.Look, axisDirection);
					xFlip = (axisDot > 0) ? -1 : 1;
					zOff = xChange * xFlip;
					break;
				case GizmoSelectedAxes.XY_AXIS:
					xOff = xChange; yOff = yChange * yFlip;
					break;
				case GizmoSelectedAxes.XZ_AXIS:
					xOff = xChange; zOff = yChange;
					break;
				case GizmoSelectedAxes.ZY_AXIS:
					zOff = xChange; yOff = yChange * yFlip;
					break;
			}

			affectedPoint.X += xOff;
			affectedPoint.Y += yOff;
			affectedPoint.Z += zOff;

			return true;
		}
	}
}
