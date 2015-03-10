﻿using System.Collections.Generic;
using System.Globalization;
using Microsoft.DirectX;
using Microsoft.DirectX.Direct3D;
using SA_Tools;
using SonicRetro.SAModel;
using SonicRetro.SAModel.Direct3D;
using SonicRetro.SAModel.SADXLVL2;
using SonicRetro.SAModel.SAEditorCommon;
using SonicRetro.SAModel.SAEditorCommon.SETEditing;
using Mesh = Microsoft.DirectX.Direct3D.Mesh;

namespace SADXObjectDefinitions.Level_Effects
{
	class WindyValley3 : LevelDefinition
	{
		Object[] models = new Object[4];
		Mesh[][] meshes = new Mesh[4][];
		Vector3 Skybox_Scale;

		public override void Init(IniLevelData data, byte act, Device dev)
		{
			SkyboxScale[] skyboxdata = SkyboxScaleList.Load("Levels/Windy Valley/Skybox Data.ini");
			if (skyboxdata.Length > act)
				Skybox_Scale = skyboxdata[act].Far.ToVector3();
			for (int i = 0; i < 4; i++)
			{
				models[i] = ObjectHelper.LoadModel("Levels/Windy Valley/Act 3/Skybox model " + (i + 1).ToString(NumberFormatInfo.InvariantInfo) + ".sa1mdl");
				meshes[i] = ObjectHelper.GetMeshes(models[i], dev);
			}
		}

		public override void Render(Device dev, EditorCamera cam)
		{
			List<RenderInfo> result = new List<RenderInfo>();
			MatrixStack transform = new MatrixStack();
			transform.Push();
			transform.NJTranslate(cam.Position);
			transform.NJScale(Skybox_Scale);
			Texture[] texs = ObjectHelper.GetTextures("WINDY_BACK3");
			for (int i = 0; i < 4; i++)
				result.AddRange(models[i].DrawModelTree(dev, transform, texs, meshes[i]));
			transform.Pop();
			RenderInfo.Draw(result, dev, cam);
		}
	}
}
